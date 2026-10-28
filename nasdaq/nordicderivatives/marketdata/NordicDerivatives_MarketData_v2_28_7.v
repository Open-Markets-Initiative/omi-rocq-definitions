From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Genium INET Auxiliary Market Data

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
  *)

Module NordicDerivativesMarketDataV2287.

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

  Module OrderBookDirectory.

    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      symbol : list byte;
      long_name : list byte;
      isin : list byte;
      financial_product : N;
      trading_currency : list byte;
      number_of_decimals_in_price : N;
      number_of_decimals_in_nominal_value : N;
      odd_lot_size : N;
      round_lot_size : N;
      block_lot_size : N;
      nominal_value : N;
      number_of_legs : N;
      underlying_order_book_id : N;
      strike_price : N;
      expiration_date : N;
      number_of_decimals_in_strike_price : N;
      put_or_call : N;
      notation_date : N;
      first_trading_date_and_time : N;
      last_trading_date_and_time : N;
      country_id : N;
      market_id : N;
      physical_delivery : N;
      option_style : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 32 /\
      Datatypes.length (long_name record) = 32 /\
      Datatypes.length (isin record) = 12 /\
      (financial_product record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_currency record) = 3 /\
      (number_of_decimals_in_price record < 256 ^ N.of_nat 2)%N /\
      (number_of_decimals_in_nominal_value record < 256 ^ N.of_nat 2)%N /\
      (odd_lot_size record < 256 ^ N.of_nat 4)%N /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      (block_lot_size record < 256 ^ N.of_nat 4)%N /\
      (nominal_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_legs record < 256 ^ N.of_nat 1)%N /\
      (underlying_order_book_id record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (expiration_date record < 256 ^ N.of_nat 4)%N /\
      (number_of_decimals_in_strike_price record < 256 ^ N.of_nat 2)%N /\
      (put_or_call record < 256 ^ N.of_nat 1)%N /\
      (notation_date record < 256 ^ N.of_nat 4)%N /\
      (first_trading_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (last_trading_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (country_id record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 1)%N /\
      (physical_delivery record < 256 ^ N.of_nat 1)%N /\
      (option_style record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 32 (symbol record) ++
      encode_bytes 32 (long_name record) ++
      encode_bytes 12 (isin record) ++
      encode_uint 1 (financial_product record) ++
      encode_bytes 3 (trading_currency record) ++
      encode_uint 2 (number_of_decimals_in_price record) ++
      encode_uint 2 (number_of_decimals_in_nominal_value record) ++
      encode_uint 4 (odd_lot_size record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_uint 4 (block_lot_size record) ++
      encode_uint 8 (nominal_value record) ++
      encode_uint 1 (number_of_legs record) ++
      encode_uint 4 (underlying_order_book_id record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 4 (expiration_date record) ++
      encode_uint 2 (number_of_decimals_in_strike_price record) ++
      encode_uint 1 (put_or_call record) ++
      encode_uint 4 (notation_date record) ++
      encode_uint 8 (first_trading_date_and_time record) ++
      encode_uint 8 (last_trading_date_and_time record) ++
      encode_uint 1 (country_id record) ++
      encode_uint 1 (market_id record) ++
      encode_uint 1 (physical_delivery record) ++
      encode_uint 2 (option_style record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (long_name_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (isin_value, bytes) =>
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
                                          | Some (odd_lot_size_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (round_lot_size_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (block_lot_size_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (nominal_value_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (number_of_legs_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (underlying_order_book_id_value, bytes) =>
                                                                  match decode_uint 4 bytes with
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
                                                                              | Some (put_or_call_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (notation_date_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (first_trading_date_and_time_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (last_trading_date_and_time_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (country_id_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (market_id_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (physical_delivery_value, bytes) =>
                                                                                                          match decode_uint 2 bytes with
                                                                                                          | None => None
                                                                                                          | Some (option_style_value, bytes) =>
                                                                                                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; symbol := symbol_value; long_name := long_name_value; isin := isin_value; financial_product := financial_product_value; trading_currency := trading_currency_value; number_of_decimals_in_price := number_of_decimals_in_price_value; number_of_decimals_in_nominal_value := number_of_decimals_in_nominal_value_value; odd_lot_size := odd_lot_size_value; round_lot_size := round_lot_size_value; block_lot_size := block_lot_size_value; nominal_value := nominal_value_value; number_of_legs := number_of_legs_value; underlying_order_book_id := underlying_order_book_id_value; strike_price := strike_price_value; expiration_date := expiration_date_value; number_of_decimals_in_strike_price := number_of_decimals_in_strike_price_value; put_or_call := put_or_call_value; notation_date := notation_date_value; first_trading_date_and_time := first_trading_date_and_time_value; last_trading_date_and_time := last_trading_date_and_time_value; country_id := country_id_value; market_id := market_id_value; physical_delivery := physical_delivery_value; option_style := option_style_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 153.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookDirectory.

  Module MarketDirectory.

    Record t := {
      timestamp_nanoseconds : N;
      country_id : N;
      market_id : N;
      market_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (country_id record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_name record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 1 (country_id record) ++
      encode_uint 1 (market_id record) ++
      encode_bytes 32 (market_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (country_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (market_id_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (market_name_value, bytes) =>
                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; country_id := country_id_value; market_id := market_id_value; market_name := market_name_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketDirectory.

  Module CombinationOrderBookLegDirectory.

    (** Combination Order book Directory Message *)
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

  End CombinationOrderBookLegDirectory.

  Module TickSizeTableEntry.

    (** L - Tick Size Message. *)
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
      (price_from record < 256 ^ N.of_nat 4)%N /\
      (price_to record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (tick_size record) ++
      encode_uint 4 (price_from record) ++
      encode_uint 4 (price_to record).

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
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_from_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_to_value, bytes) =>
                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; tick_size := tick_size_value; price_from := price_from_value; price_to := price_to_value |}, bytes)
                      end
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

  End TickSizeTableEntry.

  Module SystemEventMessage.

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

  Module ReportedTrade.

    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      traded_quantity : N;
      match_id : N;
      combo_group_id : N;
      time_of_trade_execution : N;
      time_of_trade_agreement : N;
      time_of_trade_dissemination : N;
      trade_price : N;
      trade_type : N;
      reserved_alpha_7 : list byte;
      second_reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (traded_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      (time_of_trade_execution record < 256 ^ N.of_nat 8)%N /\
      (time_of_trade_agreement record < 256 ^ N.of_nat 8)%N /\
      (time_of_trade_dissemination record < 256 ^ N.of_nat 8)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (trade_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (reserved_alpha_7 record) = 7 /\
      Datatypes.length (second_reserved record) = 7.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (traded_quantity record) ++
      encode_uint 8 (match_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_uint 8 (time_of_trade_execution record) ++
      encode_uint 8 (time_of_trade_agreement record) ++
      encode_uint 8 (time_of_trade_dissemination record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 2 (trade_type record) ++
      encode_bytes 7 (reserved_alpha_7 record) ++
      encode_bytes 7 (second_reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (traded_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (combo_group_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (time_of_trade_execution_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (time_of_trade_agreement_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (time_of_trade_dissemination_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (trade_type_value, bytes) =>
                                              match decode_bytes 7 bytes with
                                              | None => None
                                              | Some (reserved_alpha_7_value, bytes) =>
                                                  match decode_bytes 7 bytes with
                                                  | None => None
                                                  | Some (second_reserved_value, bytes) =>
                                                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; traded_quantity := traded_quantity_value; match_id := match_id_value; combo_group_id := combo_group_id_value; time_of_trade_execution := time_of_trade_execution_value; time_of_trade_agreement := time_of_trade_agreement_value; time_of_trade_dissemination := time_of_trade_dissemination_value; trade_price := trade_price_value; trade_type := trade_type_value; reserved_alpha_7 := reserved_alpha_7_value; second_reserved := second_reserved_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReportedTrade.

  Module BrokenTradeMessage.

    Record t := {
      timestamp_nanoseconds : N;
      match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 8 (match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (match_id_value, bytes) =>
              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; match_id := match_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End BrokenTradeMessage.

  Module QuoteRequestMessage.

    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      reserved_alpha_7 : list byte;
      reserved_alpha_5 : list byte;
      reserved_alpha_1 : list byte;
      side : list byte;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_alpha_7 record) = 7 /\
      Datatypes.length (reserved_alpha_5 record) = 5 /\
      Datatypes.length (reserved_alpha_1 record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 7 (reserved_alpha_7 record) ++
      encode_bytes 5 (reserved_alpha_5 record) ++
      encode_bytes 1 (reserved_alpha_1 record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (reserved_alpha_7_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (reserved_alpha_5_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_alpha_1_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; reserved_alpha_7 := reserved_alpha_7_value; reserved_alpha_5 := reserved_alpha_5_value; reserved_alpha_1 := reserved_alpha_1_value; side := side_value; quantity := quantity_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRequestMessage.

  Module OpenInterestMesssage.

    (** o - Open Interest Message. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      open_interest : N;
      previous_trading_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 8)%N /\
      (previous_trading_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (open_interest record) ++
      encode_uint 4 (previous_trading_date record).

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
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (previous_trading_date_value, bytes) =>
                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; open_interest := open_interest_value; previous_trading_date := previous_trading_date_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End OpenInterestMesssage.

  Module PriceMessage.

    Record t := {
      timestamp_nanoseconds : N;
      price_type : list byte;
      order_book_id : N;
      price_price_4 : N;
      price_source : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_type record) = 1 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (price_price_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_source record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 1 (price_type record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 4 (price_price_4 record) ++
      encode_bytes 1 (price_source record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_price_4_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (price_source_value, bytes) =>
                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; price_type := price_type_value; order_book_id := order_book_id_value; price_price_4 := price_price_4_value; price_source := price_source_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceMessage.

  Module MarketByLevelMessage.

    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      last_message : N;
      level_update_action : N;
      max_depth : N;
      level_update : N;
      entry_type : list byte;
      market_by_level_price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (last_message record < 256 ^ N.of_nat 1)%N /\
      (level_update_action record < 256 ^ N.of_nat 1)%N /\
      (max_depth record < 256 ^ N.of_nat 2)%N /\
      (level_update record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (entry_type record) = 1 /\
      (market_by_level_price record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 1 (last_message record) ++
      encode_uint 1 (level_update_action record) ++
      encode_uint 2 (max_depth record) ++
      encode_uint 2 (level_update record) ++
      encode_bytes 1 (entry_type record) ++
      encode_uint 4 (market_by_level_price record) ++
      encode_uint 8 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (last_message_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (level_update_action_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (max_depth_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (level_update_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (entry_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (market_by_level_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (quantity_value, bytes) =>
                                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; last_message := last_message_value; level_update_action := level_update_action_value; max_depth := max_depth_value; level_update := level_update_value; entry_type := entry_type_value; market_by_level_price := market_by_level_price_value; quantity := quantity_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketByLevelMessage.

  Module UnderlyingPriceMessage.

    Record t := {
      timestamp_nanoseconds : N;
      underlying_order_book_id : N;
      bid_price : N;
      ask_price : N;
      closing_price : N;
      opening_price : N;
      high_price : N;
      low_price : N;
      last_price : N;
      turnover : N;
      best_bid_volume : N;
      best_ask_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (underlying_order_book_id record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (closing_price record < 256 ^ N.of_nat 4)%N /\
      (opening_price record < 256 ^ N.of_nat 4)%N /\
      (high_price record < 256 ^ N.of_nat 4)%N /\
      (low_price record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (best_bid_volume record < 256 ^ N.of_nat 8)%N /\
      (best_ask_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (underlying_order_book_id record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 4 (closing_price record) ++
      encode_uint 4 (opening_price record) ++
      encode_uint 4 (high_price record) ++
      encode_uint 4 (low_price record) ++
      encode_uint 4 (last_price record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 8 (best_bid_volume record) ++
      encode_uint 8 (best_ask_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_order_book_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bid_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ask_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (opening_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (high_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (low_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (turnover_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (best_bid_volume_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (best_ask_volume_value, bytes) =>
                                                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; underlying_order_book_id := underlying_order_book_id_value; bid_price := bid_price_value; ask_price := ask_price_value; closing_price := closing_price_value; opening_price := opening_price_value; high_price := high_price_value; low_price := low_price_value; last_price := last_price_value; turnover := turnover_value; best_bid_volume := best_bid_volume_value; best_ask_volume := best_ask_volume_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End UnderlyingPriceMessage.

End NordicDerivativesMarketDataV2287.
