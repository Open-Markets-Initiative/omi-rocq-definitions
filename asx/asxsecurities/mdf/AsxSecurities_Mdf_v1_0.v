From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Australian Securities Exchange Trade Market Data Feed

    Generated from the binary model. Every record is a run of fields, and carries the two
    theorems the model's rules call for: an encoding is as wide as its fields say, and
    decoding what was encoded gives the record back and leaves the bytes after it alone.

    A field is a number of its width, a run of bytes kept as they are, or a record nested
    in it. A number's width bounds it, which the record's own bound predicate states, and
    the round trip asks for that predicate - a field is an N, so the bound is not in the
    type. Text and reserved runs are kept byte for byte, so what is decoded encodes back
    unchanged.

    Each record is a module of its own, so two messages may both have a price and a
    consumer may read either.

    What this definition does not state, and the model does:
      - the dispatch that chooses a message by its type
      - a run counted by a field

    License: MIT No Attribution
  *)

Module AsxSecuritiesMdfV10.

  Module PacketHeader.

    (** Itch Mold Udp 64 Packet Header *)
    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module MessageHeader.

    (** Mold Udp 64 Message Header *)
    Record t := {
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module SecondsMessage.

    (** Sent every second for which at least one MDF message is being generated. *)
    Record t := {
      second : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (second record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (second_value, bytes) =>
          Some ({| second := second_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SecondsMessage.

  Module OrderBookDirectoryMessage.

    (** Disseminated at the start of each trading day for all active securities, including halted securities. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      partition_id : N;
      symbol : list byte;
      long_name : list byte;
      isin : list byte;
      asset_name : list byte;
      financial_product : N;
      trading_currency : list byte;
      number_of_decimals_in_price : N;
      number_of_decimals_in_nominal_value : N;
      round_lot_size : N;
      nominal_value : N;
      number_of_legs : N;
      commodity_code : N;
      strike_price : N;
      expiration_date : N;
      number_of_decimals_in_strike_price : N;
      option_type : N;
      market_id : N;
      exchange_id : N;
      number_of_decimals_in : N;
      sector_code : list byte;
      number_of_tradable_equities : N;
      number_of_outstanding_equities : N;
      last_traded_date : N;
      contract_multiplier : N;
      multiplier : N;
      decimals_in_multiplier : N;
      min_order_quantity : N;
      max_order_quantity : N;
      number_of_settlement_days : N;
      primary : N;
      test_order_book : N;
      alias_name : list byte;
      settlement_date : N;
      tradable : N;
      externally_price_sourced : N;
      deliverable : N;
      price_unit : N;
      issuer : list byte;
      foreign_ownership_restriction : N;
      last_trading_time : list byte;
      option_style : N;
      minimum_value_for_initial_trade_report : N;
      cfi_code : list byte;
      upper_level_series : list byte;
      upper_series_level_order_book_id : N;
      instrument_type : list byte;
      status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (partition_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (symbol record) = 32 /\
      Datatypes.length (long_name record) = 32 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (asset_name record) = 32 /\
      (financial_product record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_currency record) = 3 /\
      (number_of_decimals_in_price record < 256 ^ N.of_nat 2)%N /\
      (number_of_decimals_in_nominal_value record < 256 ^ N.of_nat 2)%N /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      (nominal_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_legs record < 256 ^ N.of_nat 1)%N /\
      (commodity_code record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (expiration_date record < 256 ^ N.of_nat 4)%N /\
      (number_of_decimals_in_strike_price record < 256 ^ N.of_nat 2)%N /\
      (option_type record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (exchange_id record < 256 ^ N.of_nat 4)%N /\
      (number_of_decimals_in record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sector_code record) = 4 /\
      (number_of_tradable_equities record < 256 ^ N.of_nat 8)%N /\
      (number_of_outstanding_equities record < 256 ^ N.of_nat 8)%N /\
      (last_traded_date record < 256 ^ N.of_nat 4)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 8)%N /\
      (multiplier record < 256 ^ N.of_nat 8)%N /\
      (decimals_in_multiplier record < 256 ^ N.of_nat 2)%N /\
      (min_order_quantity record < 256 ^ N.of_nat 8)%N /\
      (max_order_quantity record < 256 ^ N.of_nat 8)%N /\
      (number_of_settlement_days record < 256 ^ N.of_nat 4)%N /\
      (primary record < 256 ^ N.of_nat 1)%N /\
      (test_order_book record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (alias_name record) = 32 /\
      (settlement_date record < 256 ^ N.of_nat 4)%N /\
      (tradable record < 256 ^ N.of_nat 1)%N /\
      (externally_price_sourced record < 256 ^ N.of_nat 1)%N /\
      (deliverable record < 256 ^ N.of_nat 1)%N /\
      (price_unit record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (issuer record) = 32 /\
      (foreign_ownership_restriction record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (last_trading_time record) = 6 /\
      (option_style record < 256 ^ N.of_nat 1)%N /\
      (minimum_value_for_initial_trade_report record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cfi_code record) = 6 /\
      Datatypes.length (upper_level_series record) = 32 /\
      (upper_series_level_order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (instrument_type record) = 4 /\
      Datatypes.length (status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 1 (partition_id record) ++
      encode_bytes 32 (symbol record) ++
      encode_bytes 32 (long_name record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 32 (asset_name record) ++
      encode_uint 1 (financial_product record) ++
      encode_bytes 3 (trading_currency record) ++
      encode_uint 2 (number_of_decimals_in_price record) ++
      encode_uint 2 (number_of_decimals_in_nominal_value record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_uint 8 (nominal_value record) ++
      encode_uint 1 (number_of_legs record) ++
      encode_uint 4 (commodity_code record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 4 (expiration_date record) ++
      encode_uint 2 (number_of_decimals_in_strike_price record) ++
      encode_uint 1 (option_type record) ++
      encode_uint 4 (market_id record) ++
      encode_uint 4 (exchange_id record) ++
      encode_uint 2 (number_of_decimals_in record) ++
      encode_bytes 4 (sector_code record) ++
      encode_uint 8 (number_of_tradable_equities record) ++
      encode_uint 8 (number_of_outstanding_equities record) ++
      encode_uint 4 (last_traded_date record) ++
      encode_uint 8 (contract_multiplier record) ++
      encode_uint 8 (multiplier record) ++
      encode_uint 2 (decimals_in_multiplier record) ++
      encode_uint 8 (min_order_quantity record) ++
      encode_uint 8 (max_order_quantity record) ++
      encode_uint 4 (number_of_settlement_days record) ++
      encode_uint 1 (primary record) ++
      encode_uint 1 (test_order_book record) ++
      encode_bytes 32 (alias_name record) ++
      encode_uint 4 (settlement_date record) ++
      encode_uint 1 (tradable record) ++
      encode_uint 1 (externally_price_sourced record) ++
      encode_uint 1 (deliverable record) ++
      encode_uint 1 (price_unit record) ++
      encode_bytes 32 (issuer record) ++
      encode_uint 1 (foreign_ownership_restriction record) ++
      encode_bytes 6 (last_trading_time record) ++
      encode_uint 1 (option_style record) ++
      encode_uint 8 (minimum_value_for_initial_trade_report record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_bytes 32 (upper_level_series record) ++
      encode_uint 4 (upper_series_level_order_book_id record) ++
      encode_bytes 4 (instrument_type record) ++
      encode_bytes 1 (status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (partition_id_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_bytes 32 bytes with
                      | None => None
                      | Some (long_name_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (isin_value, bytes) =>
                              match decode_bytes 32 bytes with
                              | None => None
                              | Some (asset_name_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (financial_product_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (trading_currency_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (number_of_decimals_in_price_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (number_of_decimals_in_nominal_value_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (round_lot_size_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (nominal_value_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (number_of_legs_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (commodity_code_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (strike_price_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (expiration_date_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (number_of_decimals_in_strike_price_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (option_type_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (market_id_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (exchange_id_value, bytes) =>
                                                                                          match decode_uint 2 bytes with
                                                                                          | None => None
                                                                                          | Some (number_of_decimals_in_value, bytes) =>
                                                                                              match decode_bytes 4 bytes with
                                                                                              | None => None
                                                                                              | Some (sector_code_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (number_of_tradable_equities_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (number_of_outstanding_equities_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (last_traded_date_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (contract_multiplier_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (multiplier_value, bytes) =>
                                                                                                                      match decode_uint 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (decimals_in_multiplier_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (min_order_quantity_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (max_order_quantity_value, bytes) =>
                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (number_of_settlement_days_value, bytes) =>
                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (primary_value, bytes) =>
                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (test_order_book_value, bytes) =>
                                                                                                                                              match decode_bytes 32 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (alias_name_value, bytes) =>
                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (settlement_date_value, bytes) =>
                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (tradable_value, bytes) =>
                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (externally_price_sourced_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (deliverable_value, bytes) =>
                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (price_unit_value, bytes) =>
                                                                                                                                                                      match decode_bytes 32 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (issuer_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (foreign_ownership_restriction_value, bytes) =>
                                                                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (last_trading_time_value, bytes) =>
                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (option_style_value, bytes) =>
                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (minimum_value_for_initial_trade_report_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 6 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (cfi_code_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 32 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (upper_level_series_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (upper_series_level_order_book_id_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (instrument_type_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (status_value, bytes) =>
                                                                                                                                                                                                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; partition_id := partition_id_value; symbol := symbol_value; long_name := long_name_value; isin := isin_value; asset_name := asset_name_value; financial_product := financial_product_value; trading_currency := trading_currency_value; number_of_decimals_in_price := number_of_decimals_in_price_value; number_of_decimals_in_nominal_value := number_of_decimals_in_nominal_value_value; round_lot_size := round_lot_size_value; nominal_value := nominal_value_value; number_of_legs := number_of_legs_value; commodity_code := commodity_code_value; strike_price := strike_price_value; expiration_date := expiration_date_value; number_of_decimals_in_strike_price := number_of_decimals_in_strike_price_value; option_type := option_type_value; market_id := market_id_value; exchange_id := exchange_id_value; number_of_decimals_in := number_of_decimals_in_value; sector_code := sector_code_value; number_of_tradable_equities := number_of_tradable_equities_value; number_of_outstanding_equities := number_of_outstanding_equities_value; last_traded_date := last_traded_date_value; contract_multiplier := contract_multiplier_value; multiplier := multiplier_value; decimals_in_multiplier := decimals_in_multiplier_value; min_order_quantity := min_order_quantity_value; max_order_quantity := max_order_quantity_value; number_of_settlement_days := number_of_settlement_days_value; primary := primary_value; test_order_book := test_order_book_value; alias_name := alias_name_value; settlement_date := settlement_date_value; tradable := tradable_value; externally_price_sourced := externally_price_sourced_value; deliverable := deliverable_value; price_unit := price_unit_value; issuer := issuer_value; foreign_ownership_restriction := foreign_ownership_restriction_value; last_trading_time := last_trading_time_value; option_style := option_style_value; minimum_value_for_initial_trade_report := minimum_value_for_initial_trade_report_value; cfi_code := cfi_code_value; upper_level_series := upper_level_series_value; upper_series_level_order_book_id := upper_series_level_order_book_id_value; instrument_type := instrument_type_value; status := status_value |}, bytes)
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 366.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 bound_49]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_bytes by exact bound_45.
      rewrite decode_encode_bytes by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookDirectoryMessage.

  Module ExchangeDirectoryMessage.

    (** Disseminated at the start of each trading day for all active Exchanges in the system. *)
    Record t := {
      timestamp_nanoseconds : N;
      exchange_id : N;
      exchange_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (exchange_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exchange_name record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (exchange_id record) ++
      encode_bytes 32 (exchange_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (exchange_name_value, bytes) =>
                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; exchange_id := exchange_id_value; exchange_name := exchange_name_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExchangeDirectoryMessage.

  Module MarketDirectoryMessage.

    (** Disseminated at the start of each trading day for all active Markets in the system. *)
    Record t := {
      timestamp_nanoseconds : N;
      market_id : N;
      market_name : list byte;
      market_type : N;
      index_market : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_name record) = 32 /\
      (market_type record < 256 ^ N.of_nat 1)%N /\
      (index_market record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (market_id record) ++
      encode_bytes 32 (market_name record) ++
      encode_uint 1 (market_type record) ++
      encode_uint 1 (index_market record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (market_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (market_name_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_type_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (index_market_value, bytes) =>
                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; market_id := market_id_value; market_name := market_name_value; market_type := market_type_value; index_market := index_market_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketDirectoryMessage.

  Module CombinationOrderBookLegDirectoryMessage.

    (** Provides a mapping between a combination order book and one of the combination leg order books. *)
    Record t := {
      timestamp_nanoseconds : N;
      combination_order_book_id : N;
      leg_order_book_id : N;
      leg_side : list byte;
      leg_ratio : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (combination_order_book_id record < 256 ^ N.of_nat 4)%N /\
      (leg_order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side record) = 1 /\
      (leg_ratio record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (combination_order_book_id record) ++
      encode_uint 4 (leg_order_book_id record) ++
      encode_bytes 1 (leg_side record) ++
      encode_uint 4 (leg_ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (combination_order_book_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (leg_order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (leg_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (leg_ratio_value, bytes) =>
                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; combination_order_book_id := combination_order_book_id_value; leg_order_book_id := leg_order_book_id_value; leg_side := leg_side_value; leg_ratio := leg_ratio_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CombinationOrderBookLegDirectoryMessage.

  Module TickSizeTableEntryMessage.

    (** Contains information on a tick size for a price range. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      tick_size : N;
      price_from : N;
      price_to : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N /\
      (price_from record < 256 ^ N.of_nat 8)%N /\
      (price_to record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (tick_size record) ++
      encode_uint 8 (price_from record) ++
      encode_uint 8 (price_to record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tick_size_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_from_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_to_value, bytes) =>
                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; tick_size := tick_size_value; price_from := price_from_value; price_to := price_to_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TickSizeTableEntryMessage.

  Module CorporateActionEntryMessage.

    (** Displays the entries of assigned Corporate Action Codes to Order Books. *)
    Record t := {
      timestamp_nanoseconds : N;
      corporate_action_id : N;
      order_book_id : N;
      corporate_action_code : list byte;
      corporate_action_type : list byte;
      start_date : N;
      end_date : N;
      record_date : N;
      corporate_action_status : N;
      action : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (corporate_action_id record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (corporate_action_code record) = 4 /\
      Datatypes.length (corporate_action_type record) = 1 /\
      (start_date record < 256 ^ N.of_nat 4)%N /\
      (end_date record < 256 ^ N.of_nat 4)%N /\
      (record_date record < 256 ^ N.of_nat 4)%N /\
      (corporate_action_status record < 256 ^ N.of_nat 1)%N /\
      (action record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (corporate_action_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 4 (corporate_action_code record) ++
      encode_bytes 1 (corporate_action_type record) ++
      encode_uint 4 (start_date record) ++
      encode_uint 4 (end_date record) ++
      encode_uint 4 (record_date record) ++
      encode_uint 1 (corporate_action_status record) ++
      encode_uint 1 (action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (corporate_action_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (corporate_action_code_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (corporate_action_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (start_date_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (end_date_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (record_date_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (corporate_action_status_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (action_value, bytes) =>
                                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; corporate_action_id := corporate_action_id_value; order_book_id := order_book_id_value; corporate_action_code := corporate_action_code_value; corporate_action_type := corporate_action_type_value; start_date := start_date_value; end_date := end_date_value; record_date := record_date_value; corporate_action_status := corporate_action_status_value; action := action_value |}, bytes)
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CorporateActionEntryMessage.

  Module OrderBookDirectoryExtensionMessage.

    (** Provides additional information that are valid only for Fixed Income instruments; sent for all instruments. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      accrued_interest_rounding : N;
      accrued_interest_updown : N;
      calculation_convention : N;
      clean_price_rounding : N;
      clean_price_updown : N;
      coupon_frequency : N;
      coupon_interest : N;
      coupon_from_date : N;
      issue_date : N;
      maturity_date : N;
      day_calculation_rule : N;
      day_count_convention : N;
      ex_coupon_period : N;
      dividend : N;
      fixed_income_type : N;
      rate_determination_days : N;
      yield_convention : N;
      end_of_month_count_convention : N;
      first_settlement_date : N;
      coupon_div_date : N;
      date_books_close : N;
      effective_expiration_date : N;
      proceed_date : N;
      set_end_consideration : N;
      set_start_consideration : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (accrued_interest_rounding record < 256 ^ N.of_nat 4)%N /\
      (accrued_interest_updown record < 256 ^ N.of_nat 1)%N /\
      (calculation_convention record < 256 ^ N.of_nat 1)%N /\
      (clean_price_rounding record < 256 ^ N.of_nat 4)%N /\
      (clean_price_updown record < 256 ^ N.of_nat 1)%N /\
      (coupon_frequency record < 256 ^ N.of_nat 4)%N /\
      (coupon_interest record < 256 ^ N.of_nat 8)%N /\
      (coupon_from_date record < 256 ^ N.of_nat 4)%N /\
      (issue_date record < 256 ^ N.of_nat 4)%N /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (day_calculation_rule record < 256 ^ N.of_nat 1)%N /\
      (day_count_convention record < 256 ^ N.of_nat 1)%N /\
      (ex_coupon_period record < 256 ^ N.of_nat 4)%N /\
      (dividend record < 256 ^ N.of_nat 8)%N /\
      (fixed_income_type record < 256 ^ N.of_nat 1)%N /\
      (rate_determination_days record < 256 ^ N.of_nat 4)%N /\
      (yield_convention record < 256 ^ N.of_nat 4)%N /\
      (end_of_month_count_convention record < 256 ^ N.of_nat 4)%N /\
      (first_settlement_date record < 256 ^ N.of_nat 4)%N /\
      (coupon_div_date record < 256 ^ N.of_nat 4)%N /\
      (date_books_close record < 256 ^ N.of_nat 4)%N /\
      (effective_expiration_date record < 256 ^ N.of_nat 4)%N /\
      (proceed_date record < 256 ^ N.of_nat 4)%N /\
      (set_end_consideration record < 256 ^ N.of_nat 1)%N /\
      (set_start_consideration record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 4 (accrued_interest_rounding record) ++
      encode_uint 1 (accrued_interest_updown record) ++
      encode_uint 1 (calculation_convention record) ++
      encode_uint 4 (clean_price_rounding record) ++
      encode_uint 1 (clean_price_updown record) ++
      encode_uint 4 (coupon_frequency record) ++
      encode_uint 8 (coupon_interest record) ++
      encode_uint 4 (coupon_from_date record) ++
      encode_uint 4 (issue_date record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 1 (day_calculation_rule record) ++
      encode_uint 1 (day_count_convention record) ++
      encode_uint 4 (ex_coupon_period record) ++
      encode_uint 8 (dividend record) ++
      encode_uint 1 (fixed_income_type record) ++
      encode_uint 4 (rate_determination_days record) ++
      encode_uint 4 (yield_convention record) ++
      encode_uint 4 (end_of_month_count_convention record) ++
      encode_uint 4 (first_settlement_date record) ++
      encode_uint 4 (coupon_div_date record) ++
      encode_uint 4 (date_books_close record) ++
      encode_uint 4 (effective_expiration_date record) ++
      encode_uint 4 (proceed_date record) ++
      encode_uint 1 (set_end_consideration record) ++
      encode_uint 1 (set_start_consideration record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (accrued_interest_rounding_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (accrued_interest_updown_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (calculation_convention_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (clean_price_rounding_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (clean_price_updown_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (coupon_frequency_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (coupon_interest_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (coupon_from_date_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (issue_date_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (maturity_date_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (day_calculation_rule_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (day_count_convention_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (ex_coupon_period_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (dividend_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (fixed_income_type_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (rate_determination_days_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (yield_convention_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (end_of_month_count_convention_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (first_settlement_date_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (coupon_div_date_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (date_books_close_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (effective_expiration_date_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (proceed_date_value, bytes) =>
                                                                                                          match decode_uint 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (set_end_consideration_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (set_start_consideration_value, bytes) =>
                                                                                                                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; accrued_interest_rounding := accrued_interest_rounding_value; accrued_interest_updown := accrued_interest_updown_value; calculation_convention := calculation_convention_value; clean_price_rounding := clean_price_rounding_value; clean_price_updown := clean_price_updown_value; coupon_frequency := coupon_frequency_value; coupon_interest := coupon_interest_value; coupon_from_date := coupon_from_date_value; issue_date := issue_date_value; maturity_date := maturity_date_value; day_calculation_rule := day_calculation_rule_value; day_count_convention := day_count_convention_value; ex_coupon_period := ex_coupon_period_value; dividend := dividend_value; fixed_income_type := fixed_income_type_value; rate_determination_days := rate_determination_days_value; yield_convention := yield_convention_value; end_of_month_count_convention := end_of_month_count_convention_value; first_settlement_date := first_settlement_date_value; coupon_div_date := coupon_div_date_value; date_books_close := date_books_close_value; effective_expiration_date := effective_expiration_date_value; proceed_date := proceed_date_value; set_end_consideration := set_end_consideration_value; set_start_consideration := set_start_consideration_value |}, bytes)
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 92.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderBookDirectoryExtensionMessage.

  Module SystemEventMessage.

    (** Used to signal a market or data feed handler event. *)
    Record t := {
      timestamp_nanoseconds : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; event_code := event_code_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module OrderBookStateMessage.

    (** Relays information on state changes. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      state_name : list byte;
      display_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (state_name record) = 20 /\
      Datatypes.length (display_name record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 20 (state_name record) ++
      encode_bytes 20 (display_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (state_name_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (display_name_value, bytes) =>
                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; state_name := state_name_value; display_name := display_name_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookStateMessage.

  Module BusinessDateMessage.

    (** Relays information on the current business date. *)
    Record t := {
      timestamp_nanoseconds : N;
      business_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (business_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (business_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (business_date_value, bytes) =>
              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; business_date := business_date_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BusinessDateMessage.

  Module InstrumentStatusMessage.

    (** Received when the State of an Instrument is changed at any of the applicable levels. *)
    Record t := {
      timestamp_nanoseconds : N;
      trading_state_name : list byte;
      instrument_state_level : N;
      name_of_the_instrument_state_level : list byte;
      start_date : N;
      start_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_state_name record) = 20 /\
      (instrument_state_level record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (name_of_the_instrument_state_level record) = 32 /\
      (start_date record < 256 ^ N.of_nat 4)%N /\
      (start_time record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 20 (trading_state_name record) ++
      encode_uint 1 (instrument_state_level record) ++
      encode_bytes 32 (name_of_the_instrument_state_level record) ++
      encode_uint 4 (start_date record) ++
      encode_uint 4 (start_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (trading_state_name_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (instrument_state_level_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (name_of_the_instrument_state_level_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (start_date_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (start_time_value, bytes) =>
                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; trading_state_name := trading_state_name_value; instrument_state_level := instrument_state_level_value; name_of_the_instrument_state_level := name_of_the_instrument_state_level_value; start_date := start_date_value; start_time := start_time_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentStatusMessage.

  Module EquilibriumPriceMessage.

    (** Used when auctions occur; provides the changes in equilibrium price. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      available_bid_quantity_at_equilibrium_price : N;
      available_ask_quantity_at_equilibrium_price : N;
      equilibrium_price : N;
      best_bid_price : N;
      best_ask_price : N;
      best_bid_quantity : N;
      best_ask_quantity : N;
      equilibrium_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (available_bid_quantity_at_equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (available_ask_quantity_at_equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (best_bid_price record < 256 ^ N.of_nat 8)%N /\
      (best_ask_price record < 256 ^ N.of_nat 8)%N /\
      (best_bid_quantity record < 256 ^ N.of_nat 8)%N /\
      (best_ask_quantity record < 256 ^ N.of_nat 8)%N /\
      (equilibrium_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (available_bid_quantity_at_equilibrium_price record) ++
      encode_uint 8 (available_ask_quantity_at_equilibrium_price record) ++
      encode_uint 8 (equilibrium_price record) ++
      encode_uint 8 (best_bid_price record) ++
      encode_uint 8 (best_ask_price record) ++
      encode_uint 8 (best_bid_quantity record) ++
      encode_uint 8 (best_ask_quantity record) ++
      encode_uint 8 (equilibrium_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (available_bid_quantity_at_equilibrium_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (available_ask_quantity_at_equilibrium_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (equilibrium_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (best_bid_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (best_ask_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (best_bid_quantity_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (best_ask_quantity_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (equilibrium_quantity_value, bytes) =>
                                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; available_bid_quantity_at_equilibrium_price := available_bid_quantity_at_equilibrium_price_value; available_ask_quantity_at_equilibrium_price := available_ask_quantity_at_equilibrium_price_value; equilibrium_price := equilibrium_price_value; best_bid_price := best_bid_price_value; best_ask_price := best_ask_price_value; best_bid_quantity := best_bid_quantity_value; best_ask_quantity := best_ask_quantity_value; equilibrium_quantity := equilibrium_quantity_value |}, bytes)
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EquilibriumPriceMessage.

  Module TradeStatisticsMessage.

    (** Publishes Trade Statistics per Orderbook ID for the current Trading Day. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      open_price : N;
      high_price : N;
      low_price : N;
      last_price : N;
      last_auction_price : N;
      last_quantity : N;
      turnover_quantity : N;
      reported_trades_turnover_quantity : N;
      turnover_value : N;
      number_of_trades : N;
      trend_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (last_auction_price record < 256 ^ N.of_nat 8)%N /\
      (last_quantity record < 256 ^ N.of_nat 8)%N /\
      (turnover_quantity record < 256 ^ N.of_nat 8)%N /\
      (reported_trades_turnover_quantity record < 256 ^ N.of_nat 8)%N /\
      (turnover_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_trades record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trend_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (last_auction_price record) ++
      encode_uint 8 (last_quantity record) ++
      encode_uint 8 (turnover_quantity record) ++
      encode_uint 8 (reported_trades_turnover_quantity record) ++
      encode_uint 8 (turnover_value record) ++
      encode_uint 8 (number_of_trades record) ++
      encode_bytes 1 (trend_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (open_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (high_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (low_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (last_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (last_auction_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_quantity_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (turnover_quantity_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (reported_trades_turnover_quantity_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (turnover_value_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (number_of_trades_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trend_indicator_value, bytes) =>
                                                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; open_price := open_price_value; high_price := high_price_value; low_price := low_price_value; last_price := last_price_value; last_auction_price := last_auction_price_value; last_quantity := last_quantity_value; turnover_quantity := turnover_quantity_value; reported_trades_turnover_quantity := reported_trades_turnover_quantity_value; turnover_value := turnover_value_value; number_of_trades := number_of_trades_value; trend_indicator := trend_indicator_value |}, bytes)
                                                      end
                                                  end
                                              end
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 89.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeStatisticsMessage.

  Module ReferencePriceMessage.

    (** Publishes Reference Prices per Price Types. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      price_type : N;
      price : N;
      timestamp : N;
      price_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (price_type record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (price_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 1 (price_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (price_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (price_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_date_value, bytes) =>
                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; price_type := price_type_value; price := price_value; timestamp := timestamp_value; price_date := price_date_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ReferencePriceMessage.

  Module IndexMessage.

    (** Used for sending index price information. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      last_price : N;
      timestamp : N;
      change_previous : N;
      change_yesterday : N;
      trend_indicator : list byte;
      point_of_movement : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (change_previous record < 256 ^ N.of_nat 4)%N /\
      (change_yesterday record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trend_indicator record) = 1 /\
      (point_of_movement record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (change_previous record) ++
      encode_uint 4 (change_yesterday record) ++
      encode_bytes 1 (trend_indicator record) ++
      encode_uint 4 (point_of_movement record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (change_previous_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (change_yesterday_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trend_indicator_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (point_of_movement_value, bytes) =>
                                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; last_price := last_price_value; timestamp := timestamp_value; change_previous := change_previous_value; change_yesterday := change_yesterday_value; trend_indicator := trend_indicator_value; point_of_movement := point_of_movement_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexMessage.

  Module OpenInterestMessage.

    (** Publishes Open Interest. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      open_interest : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (open_interest record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (open_interest_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transact_time_value, bytes) =>
                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; open_interest := open_interest_value; transact_time := transact_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OpenInterestMessage.

  Module TradeTickerMessage.

    (** Publishes Trade Ticker. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      deal_id : N;
      deal_source : N;
      price : N;
      quantity : N;
      deal_time : N;
      action : N;
      aggressor : list byte;
      trade_report_type : N;
      printable : N;
      as_of_date : N;
      boq_list : list byte;
      participant_id_buy : list byte;
      order_id_buy : N;
      participant_id_sell : list byte;
      order_id_sell : N;
      trade_slip_number : N;
      exchange_order_type : N;
      trade_condition : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (deal_id record < 256 ^ N.of_nat 8)%N /\
      (deal_source record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (deal_time record < 256 ^ N.of_nat 8)%N /\
      (action record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (aggressor record) = 1 /\
      (trade_report_type record < 256 ^ N.of_nat 2)%N /\
      (printable record < 256 ^ N.of_nat 1)%N /\
      (as_of_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (boq_list record) = 6 /\
      Datatypes.length (participant_id_buy record) = 5 /\
      (order_id_buy record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (participant_id_sell record) = 5 /\
      (order_id_sell record < 256 ^ N.of_nat 8)%N /\
      (trade_slip_number record < 256 ^ N.of_nat 4)%N /\
      (exchange_order_type record < 256 ^ N.of_nat 4)%N /\
      (trade_condition record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (deal_id record) ++
      encode_uint 1 (deal_source record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 8 (deal_time record) ++
      encode_uint 1 (action record) ++
      encode_bytes 1 (aggressor record) ++
      encode_uint 2 (trade_report_type record) ++
      encode_uint 1 (printable record) ++
      encode_uint 4 (as_of_date record) ++
      encode_bytes 6 (boq_list record) ++
      encode_bytes 5 (participant_id_buy record) ++
      encode_uint 8 (order_id_buy record) ++
      encode_bytes 5 (participant_id_sell record) ++
      encode_uint 8 (order_id_sell record) ++
      encode_uint 4 (trade_slip_number record) ++
      encode_uint 4 (exchange_order_type record) ++
      encode_uint 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (deal_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (deal_source_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (deal_time_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (action_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (aggressor_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (trade_report_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (printable_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (as_of_date_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (boq_list_value, bytes) =>
                                                          match decode_bytes 5 bytes with
                                                          | None => None
                                                          | Some (participant_id_buy_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (order_id_buy_value, bytes) =>
                                                                  match decode_bytes 5 bytes with
                                                                  | None => None
                                                                  | Some (participant_id_sell_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (order_id_sell_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (trade_slip_number_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (exchange_order_type_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trade_condition_value, bytes) =>
                                                                                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; deal_id := deal_id_value; deal_source := deal_source_value; price := price_value; quantity := quantity_value; deal_time := deal_time_value; action := action_value; aggressor := aggressor_value; trade_report_type := trade_report_type_value; printable := printable_value; as_of_date := as_of_date_value; boq_list := boq_list_value; participant_id_buy := participant_id_buy_value; order_id_buy := order_id_buy_value; participant_id_sell := participant_id_sell_value; order_id_sell := order_id_sell_value; trade_slip_number := trade_slip_number_value; exchange_order_type := exchange_order_type_value; trade_condition := trade_condition_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 91.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeTickerMessage.

  Module PriceLimitsMessage.

    (** Provides an update to the price limits or circuit breaker limits for an order book. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      upper_limit : N;
      lower_limit : N;
      type : N;
      category : N;
      reference_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (upper_limit record < 256 ^ N.of_nat 8)%N /\
      (lower_limit record < 256 ^ N.of_nat 8)%N /\
      (type record < 256 ^ N.of_nat 1)%N /\
      (category record < 256 ^ N.of_nat 1)%N /\
      (reference_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (upper_limit record) ++
      encode_uint 8 (lower_limit record) ++
      encode_uint 1 (type record) ++
      encode_uint 1 (category record) ++
      encode_uint 8 (reference_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (upper_limit_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (lower_limit_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (type_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (category_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (reference_price_value, bytes) =>
                                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; upper_limit := upper_limit_value; lower_limit := lower_limit_value; type := type_value; category := category_value; reference_price := reference_price_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End PriceLimitsMessage.

  Module EndOfSnapshotMessage.

    (** Returns the current MDF sequence number to be used when connecting to the MDF feed (Glimpse). *)
    Record t := {
      snapshot_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (snapshot_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (snapshot_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (snapshot_sequence_number_value, bytes) =>
          Some ({| snapshot_sequence_number := snapshot_sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfSnapshotMessage.

End AsxSecuritiesMdfV10.
