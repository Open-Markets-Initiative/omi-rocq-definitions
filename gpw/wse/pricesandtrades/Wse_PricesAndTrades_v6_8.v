From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Prices and Trades

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
      - a run filling what frames it
  *)

Module WsePricesAndTradesV68.

  Module PacketHeader.

    (** All messages are preceded by a common packet header format, which section 1.1 states for every Market Information message *)
    Record t := {
      packet_length : N;
      packet_type : N;
      packet_sequence_number : N;
      send_time : N;
      service_id : N;
      delivery_flag : N;
      number_msg_entries : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_type record < 256 ^ N.of_nat 2)%N /\
      (packet_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (send_time record < 256 ^ N.of_nat 4)%N /\
      (service_id record < 256 ^ N.of_nat 2)%N /\
      (delivery_flag record < 256 ^ N.of_nat 1)%N /\
      (number_msg_entries record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_uint 2 (packet_type record) ++
      encode_uint 4 (packet_sequence_number record) ++
      encode_uint 4 (send_time record) ++
      encode_uint 2 (service_id record) ++
      encode_uint 1 (delivery_flag record) ++
      encode_uint 1 (number_msg_entries record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (packet_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (packet_sequence_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (send_time_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (service_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (delivery_flag_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (number_msg_entries_value, bytes) =>
                                  Some ({| packet_length := packet_length_value; packet_type := packet_type_value; packet_sequence_number := packet_sequence_number_value; send_time := send_time_value; service_id := service_id_value; delivery_flag := delivery_flag_value; number_msg_entries := number_msg_entries_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_size : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      encode_uint 2 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_size := message_size_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End MessageHeader.

  Module TradeFullInformationMessage.

    (** Trade full information message is sent each time a trade or a cancellation of a trade has occurred *)
    Record t := {
      symbol_index : N;
      source_time : N;
      trade_id_number : N;
      venue_of_execution : list byte;
      source_seq_num : N;
      price_notation : list byte;
      transaction_to_be_cleared : list byte;
      cumulative_quantity : N;
      highest_price : N;
      lowest_price : N;
      variation_last_price : N;
      system_id : N;
      source_time_micro_secs : N;
      price_currency : list byte;
      last_trade_indicator : list byte;
      type_of_trade : list byte;
      trade_origin : list byte;
      tick_direction : list byte;
      opening_trade_indicator : list byte;
      variation_scale_code : N;
      price_scale_code : N;
      trading_date_time : list byte;
      publication_date_time : list byte;
      instrument_id_code_type : list byte;
      instrument_id_code : list byte;
      price_ascii_ch_20 : list byte;
      quantity : list byte;
      notional_amount : list byte;
      notional_currency : list byte;
      reserved_1 : N;
      transaction_id_code : list byte;
      mmt_market_mechanism : list byte;
      mmt_trading_mode : list byte;
      mmt_algorithmic_indicator : list byte;
      mmt_modification_indicator : list byte;
      mmt_negotiation_indicator : list byte;
      mmt_special_dividend_indicator : list byte;
      mmt_contribution_to_price : list byte;
      mmt_benchmark_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (trade_id_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (venue_of_execution record) = 4 /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_notation record) = 4 /\
      Datatypes.length (transaction_to_be_cleared record) = 4 /\
      (cumulative_quantity record < 256 ^ N.of_nat 4)%N /\
      (highest_price record < 256 ^ N.of_nat 4)%N /\
      (lowest_price record < 256 ^ N.of_nat 4)%N /\
      (variation_last_price record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (price_currency record) = 3 /\
      Datatypes.length (last_trade_indicator record) = 1 /\
      Datatypes.length (type_of_trade record) = 1 /\
      Datatypes.length (trade_origin record) = 1 /\
      Datatypes.length (tick_direction record) = 1 /\
      Datatypes.length (opening_trade_indicator record) = 1 /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_date_time record) = 27 /\
      Datatypes.length (publication_date_time record) = 27 /\
      Datatypes.length (instrument_id_code_type record) = 4 /\
      Datatypes.length (instrument_id_code record) = 12 /\
      Datatypes.length (price_ascii_ch_20 record) = 20 /\
      Datatypes.length (quantity record) = 20 /\
      Datatypes.length (notional_amount record) = 20 /\
      Datatypes.length (notional_currency record) = 3 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (transaction_id_code record) = 52 /\
      Datatypes.length (mmt_market_mechanism record) = 1 /\
      Datatypes.length (mmt_trading_mode record) = 1 /\
      Datatypes.length (mmt_algorithmic_indicator record) = 4 /\
      Datatypes.length (mmt_modification_indicator record) = 4 /\
      Datatypes.length (mmt_negotiation_indicator record) = 4 /\
      Datatypes.length (mmt_special_dividend_indicator record) = 4 /\
      Datatypes.length (mmt_contribution_to_price record) = 4 /\
      Datatypes.length (mmt_benchmark_indicator record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (trade_id_number record) ++
      encode_bytes 4 (venue_of_execution record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_bytes 4 (price_notation record) ++
      encode_bytes 4 (transaction_to_be_cleared record) ++
      encode_uint 4 (cumulative_quantity record) ++
      encode_uint 4 (highest_price record) ++
      encode_uint 4 (lowest_price record) ++
      encode_uint 4 (variation_last_price record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 3 (price_currency record) ++
      encode_bytes 1 (last_trade_indicator record) ++
      encode_bytes 1 (type_of_trade record) ++
      encode_bytes 1 (trade_origin record) ++
      encode_bytes 1 (tick_direction record) ++
      encode_bytes 1 (opening_trade_indicator record) ++
      encode_uint 1 (variation_scale_code record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 27 (trading_date_time record) ++
      encode_bytes 27 (publication_date_time record) ++
      encode_bytes 4 (instrument_id_code_type record) ++
      encode_bytes 12 (instrument_id_code record) ++
      encode_bytes 20 (price_ascii_ch_20 record) ++
      encode_bytes 20 (quantity record) ++
      encode_bytes 20 (notional_amount record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 52 (transaction_id_code record) ++
      encode_bytes 1 (mmt_market_mechanism record) ++
      encode_bytes 1 (mmt_trading_mode record) ++
      encode_bytes 4 (mmt_algorithmic_indicator record) ++
      encode_bytes 4 (mmt_modification_indicator record) ++
      encode_bytes 4 (mmt_negotiation_indicator record) ++
      encode_bytes 4 (mmt_special_dividend_indicator record) ++
      encode_bytes 4 (mmt_contribution_to_price record) ++
      encode_bytes 4 (mmt_benchmark_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_id_number_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (venue_of_execution_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (source_seq_num_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (price_notation_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (transaction_to_be_cleared_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cumulative_quantity_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (highest_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (lowest_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (variation_last_price_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (system_id_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (source_time_micro_secs_value, bytes) =>
                                                          match decode_bytes 3 bytes with
                                                          | None => None
                                                          | Some (price_currency_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (last_trade_indicator_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (type_of_trade_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (trade_origin_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (tick_direction_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (opening_trade_indicator_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (variation_scale_code_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (price_scale_code_value, bytes) =>
                                                                                          match decode_bytes 27 bytes with
                                                                                          | None => None
                                                                                          | Some (trading_date_time_value, bytes) =>
                                                                                              match decode_bytes 27 bytes with
                                                                                              | None => None
                                                                                              | Some (publication_date_time_value, bytes) =>
                                                                                                  match decode_bytes 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (instrument_id_code_type_value, bytes) =>
                                                                                                      match decode_bytes 12 bytes with
                                                                                                      | None => None
                                                                                                      | Some (instrument_id_code_value, bytes) =>
                                                                                                          match decode_bytes 20 bytes with
                                                                                                          | None => None
                                                                                                          | Some (price_ascii_ch_20_value, bytes) =>
                                                                                                              match decode_bytes 20 bytes with
                                                                                                              | None => None
                                                                                                              | Some (quantity_value, bytes) =>
                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (notional_amount_value, bytes) =>
                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (notional_currency_value, bytes) =>
                                                                                                                          match decode_uint 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (reserved_1_value, bytes) =>
                                                                                                                              match decode_bytes 52 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (transaction_id_code_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (mmt_market_mechanism_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (mmt_trading_mode_value, bytes) =>
                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (mmt_algorithmic_indicator_value, bytes) =>
                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (mmt_modification_indicator_value, bytes) =>
                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (mmt_negotiation_indicator_value, bytes) =>
                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (mmt_special_dividend_indicator_value, bytes) =>
                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (mmt_contribution_to_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (mmt_benchmark_indicator_value, bytes) =>
                                                                                                                                                                  Some ({| symbol_index := symbol_index_value; source_time := source_time_value; trade_id_number := trade_id_number_value; venue_of_execution := venue_of_execution_value; source_seq_num := source_seq_num_value; price_notation := price_notation_value; transaction_to_be_cleared := transaction_to_be_cleared_value; cumulative_quantity := cumulative_quantity_value; highest_price := highest_price_value; lowest_price := lowest_price_value; variation_last_price := variation_last_price_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; price_currency := price_currency_value; last_trade_indicator := last_trade_indicator_value; type_of_trade := type_of_trade_value; trade_origin := trade_origin_value; tick_direction := tick_direction_value; opening_trade_indicator := opening_trade_indicator_value; variation_scale_code := variation_scale_code_value; price_scale_code := price_scale_code_value; trading_date_time := trading_date_time_value; publication_date_time := publication_date_time_value; instrument_id_code_type := instrument_id_code_type_value; instrument_id_code := instrument_id_code_value; price_ascii_ch_20 := price_ascii_ch_20_value; quantity := quantity_value; notional_amount := notional_amount_value; notional_currency := notional_currency_value; reserved_1 := reserved_1_value; transaction_id_code := transaction_id_code_value; mmt_market_mechanism := mmt_market_mechanism_value; mmt_trading_mode := mmt_trading_mode_value; mmt_algorithmic_indicator := mmt_algorithmic_indicator_value; mmt_modification_indicator := mmt_modification_indicator_value; mmt_negotiation_indicator := mmt_negotiation_indicator_value; mmt_special_dividend_indicator := mmt_special_dividend_indicator_value; mmt_contribution_to_price := mmt_contribution_to_price_value; mmt_benchmark_indicator := mmt_benchmark_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 272.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 bound_38]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeFullInformationMessage.

  Module PriceUpdateMessage.

    (** The Price update message contains a bid price or an ask price in case of alternative indicative price (AIP), or the modification of the last reference price on a given instrument *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      price_binary_int_4 : N;
      highest_price : N;
      lowest_price : N;
      variation_last_price : N;
      system_id : N;
      source_time_micro_secs : N;
      type_of_price : N;
      reserved_2 : N;
      price_scale_code : N;
      variation_scale_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (price_binary_int_4 record < 256 ^ N.of_nat 4)%N /\
      (highest_price record < 256 ^ N.of_nat 4)%N /\
      (lowest_price record < 256 ^ N.of_nat 4)%N /\
      (variation_last_price record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (type_of_price record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (price_binary_int_4 record) ++
      encode_uint 4 (highest_price record) ++
      encode_uint 4 (lowest_price record) ++
      encode_uint 4 (variation_last_price record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (type_of_price record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 1 (variation_scale_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_binary_int_4_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (highest_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (lowest_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (variation_last_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (system_id_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (source_time_micro_secs_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (type_of_price_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (reserved_2_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (price_scale_code_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (variation_scale_code_value, bytes) =>
                                                          Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; price_binary_int_4 := price_binary_int_4_value; highest_price := highest_price_value; lowest_price := lowest_price_value; variation_last_price := variation_last_price_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; type_of_price := type_of_price_value; reserved_2 := reserved_2_value; price_scale_code := price_scale_code_value; variation_scale_code := variation_scale_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End PriceUpdateMessage.

  Module TradePublicationMessage.

    (** A trade publication message is sent by the reporting system whenever a trade is reported *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      venue_of_execution : list byte;
      instrument_id_code_type : list byte;
      price_multiplier : N;
      system_id : N;
      source_time_micro_secs : N;
      trading_date_time : list byte;
      price_currency : list byte;
      instrument_id_code : list byte;
      publication_date_time : list byte;
      notional_currency : list byte;
      tcs_trade_id : list byte;
      price_notation : list byte;
      reserved_1 : N;
      transaction_to_be_cleared : list byte;
      mmt_benchmark_indicator : list byte;
      mmt_contribution_to_price : list byte;
      multiplier_scale_code : N;
      price_ascii_ch_20 : list byte;
      quantity : list byte;
      notional_amount : list byte;
      transaction_id_code : list byte;
      mmt_market_mechanism : list byte;
      mmt_trading_mode : list byte;
      mmt_special_dividend_indicator : list byte;
      mmt_negotiation_indicator : list byte;
      mmt_agency_cross_indicator : list byte;
      mmt_transaction_category : list byte;
      mmt_modification_indicator : list byte;
      mmt_duplicative_indicator : list byte;
      mmt_publication_mode : list byte;
      mmt_algorithmic_indicator : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (venue_of_execution record) = 4 /\
      Datatypes.length (instrument_id_code_type record) = 4 /\
      (price_multiplier record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (trading_date_time record) = 27 /\
      Datatypes.length (price_currency record) = 3 /\
      Datatypes.length (instrument_id_code record) = 12 /\
      Datatypes.length (publication_date_time record) = 27 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (tcs_trade_id record) = 16 /\
      Datatypes.length (price_notation record) = 4 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (transaction_to_be_cleared record) = 4 /\
      Datatypes.length (mmt_benchmark_indicator record) = 4 /\
      Datatypes.length (mmt_contribution_to_price record) = 4 /\
      (multiplier_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price_ascii_ch_20 record) = 20 /\
      Datatypes.length (quantity record) = 20 /\
      Datatypes.length (notional_amount record) = 20 /\
      Datatypes.length (transaction_id_code record) = 52 /\
      Datatypes.length (mmt_market_mechanism record) = 1 /\
      Datatypes.length (mmt_trading_mode record) = 1 /\
      Datatypes.length (mmt_special_dividend_indicator record) = 4 /\
      Datatypes.length (mmt_negotiation_indicator record) = 4 /\
      Datatypes.length (mmt_agency_cross_indicator record) = 4 /\
      Datatypes.length (mmt_transaction_category record) = 4 /\
      Datatypes.length (mmt_modification_indicator record) = 4 /\
      Datatypes.length (mmt_duplicative_indicator record) = 4 /\
      Datatypes.length (mmt_publication_mode record) = 4 /\
      Datatypes.length (mmt_algorithmic_indicator record) = 4 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_bytes 4 (venue_of_execution record) ++
      encode_bytes 4 (instrument_id_code_type record) ++
      encode_uint 4 (price_multiplier record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_bytes 27 (trading_date_time record) ++
      encode_bytes 3 (price_currency record) ++
      encode_bytes 12 (instrument_id_code record) ++
      encode_bytes 27 (publication_date_time record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 16 (tcs_trade_id record) ++
      encode_bytes 4 (price_notation record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 4 (transaction_to_be_cleared record) ++
      encode_bytes 4 (mmt_benchmark_indicator record) ++
      encode_bytes 4 (mmt_contribution_to_price record) ++
      encode_uint 1 (multiplier_scale_code record) ++
      encode_bytes 20 (price_ascii_ch_20 record) ++
      encode_bytes 20 (quantity record) ++
      encode_bytes 20 (notional_amount record) ++
      encode_bytes 52 (transaction_id_code record) ++
      encode_bytes 1 (mmt_market_mechanism record) ++
      encode_bytes 1 (mmt_trading_mode record) ++
      encode_bytes 4 (mmt_special_dividend_indicator record) ++
      encode_bytes 4 (mmt_negotiation_indicator record) ++
      encode_bytes 4 (mmt_agency_cross_indicator record) ++
      encode_bytes 4 (mmt_transaction_category record) ++
      encode_bytes 4 (mmt_modification_indicator record) ++
      encode_bytes 4 (mmt_duplicative_indicator record) ++
      encode_bytes 4 (mmt_publication_mode record) ++
      encode_bytes 4 (mmt_algorithmic_indicator record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (venue_of_execution_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (instrument_id_code_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_multiplier_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (system_id_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (source_time_micro_secs_value, bytes) =>
                                      match decode_bytes 27 bytes with
                                      | None => None
                                      | Some (trading_date_time_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (price_currency_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (instrument_id_code_value, bytes) =>
                                                  match decode_bytes 27 bytes with
                                                  | None => None
                                                  | Some (publication_date_time_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (notional_currency_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (tcs_trade_id_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (price_notation_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (reserved_1_value, bytes) =>
                                                                      match decode_bytes 4 bytes with
                                                                      | None => None
                                                                      | Some (transaction_to_be_cleared_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (mmt_benchmark_indicator_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (mmt_contribution_to_price_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (multiplier_scale_code_value, bytes) =>
                                                                                      match decode_bytes 20 bytes with
                                                                                      | None => None
                                                                                      | Some (price_ascii_ch_20_value, bytes) =>
                                                                                          match decode_bytes 20 bytes with
                                                                                          | None => None
                                                                                          | Some (quantity_value, bytes) =>
                                                                                              match decode_bytes 20 bytes with
                                                                                              | None => None
                                                                                              | Some (notional_amount_value, bytes) =>
                                                                                                  match decode_bytes 52 bytes with
                                                                                                  | None => None
                                                                                                  | Some (transaction_id_code_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (mmt_market_mechanism_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (mmt_trading_mode_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (mmt_special_dividend_indicator_value, bytes) =>
                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (mmt_negotiation_indicator_value, bytes) =>
                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (mmt_agency_cross_indicator_value, bytes) =>
                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (mmt_transaction_category_value, bytes) =>
                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (mmt_modification_indicator_value, bytes) =>
                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (mmt_duplicative_indicator_value, bytes) =>
                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (mmt_publication_mode_value, bytes) =>
                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (mmt_algorithmic_indicator_value, bytes) =>
                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (reserved_2_value, bytes) =>
                                                                                                                                                  Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; venue_of_execution := venue_of_execution_value; instrument_id_code_type := instrument_id_code_type_value; price_multiplier := price_multiplier_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; trading_date_time := trading_date_time_value; price_currency := price_currency_value; instrument_id_code := instrument_id_code_value; publication_date_time := publication_date_time_value; notional_currency := notional_currency_value; tcs_trade_id := tcs_trade_id_value; price_notation := price_notation_value; reserved_1 := reserved_1_value; transaction_to_be_cleared := transaction_to_be_cleared_value; mmt_benchmark_indicator := mmt_benchmark_indicator_value; mmt_contribution_to_price := mmt_contribution_to_price_value; multiplier_scale_code := multiplier_scale_code_value; price_ascii_ch_20 := price_ascii_ch_20_value; quantity := quantity_value; notional_amount := notional_amount_value; transaction_id_code := transaction_id_code_value; mmt_market_mechanism := mmt_market_mechanism_value; mmt_trading_mode := mmt_trading_mode_value; mmt_special_dividend_indicator := mmt_special_dividend_indicator_value; mmt_negotiation_indicator := mmt_negotiation_indicator_value; mmt_agency_cross_indicator := mmt_agency_cross_indicator_value; mmt_transaction_category := mmt_transaction_category_value; mmt_modification_indicator := mmt_modification_indicator_value; mmt_duplicative_indicator := mmt_duplicative_indicator_value; mmt_publication_mode := mmt_publication_mode_value; mmt_algorithmic_indicator := mmt_algorithmic_indicator_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 284.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 bound_34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradePublicationMessage.

  Module AuctionSummaryMessage.

    (** An Auction Summary message summarizes an instrument's opening or auction trades *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      first_price : N;
      last_price : N;
      highest_price : N;
      lowest_price : N;
      cumulative_quantity : N;
      variation : N;
      system_id : N;
      source_time_micro_secs : N;
      type_of_last_price : N;
      tick_direction : list byte;
      instrument_valuation_price : list byte;
      price_scale_code : N;
      variation_scale_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (first_price record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 4)%N /\
      (highest_price record < 256 ^ N.of_nat 4)%N /\
      (lowest_price record < 256 ^ N.of_nat 4)%N /\
      (cumulative_quantity record < 256 ^ N.of_nat 4)%N /\
      (variation record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (type_of_last_price record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (tick_direction record) = 1 /\
      Datatypes.length (instrument_valuation_price record) = 1 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      (variation_scale_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 4 (first_price record) ++
      encode_uint 4 (last_price record) ++
      encode_uint 4 (highest_price record) ++
      encode_uint 4 (lowest_price record) ++
      encode_uint 4 (cumulative_quantity record) ++
      encode_uint 4 (variation record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 2 (type_of_last_price record) ++
      encode_bytes 1 (tick_direction record) ++
      encode_bytes 1 (instrument_valuation_price record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_uint 1 (variation_scale_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (first_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (last_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (highest_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (lowest_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cumulative_quantity_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (variation_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (system_id_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (source_time_micro_secs_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (type_of_last_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (tick_direction_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (instrument_valuation_price_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (price_scale_code_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (variation_scale_code_value, bytes) =>
                                                                      Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; first_price := first_price_value; last_price := last_price_value; highest_price := highest_price_value; lowest_price := lowest_price_value; cumulative_quantity := cumulative_quantity_value; variation := variation_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; type_of_last_price := type_of_last_price_value; tick_direction := tick_direction_value; instrument_valuation_price := instrument_valuation_price_value; price_scale_code := price_scale_code_value; variation_scale_code := variation_scale_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionSummaryMessage.

  Module VwapClosingPriceMessage.

    (** This message contains the Volume-Weighted Average Price for an instrument, along with few statistical information related to the cumulated traded value and volume *)
    Record t := {
      symbol_index : N;
      source_time : N;
      source_seq_num : N;
      sending_indicator : N;
      closing_price_rule : N;
      closing_price : N;
      adjusted_closing_price : N;
      nb_trades : N;
      amount_traded : N;
      qty_shares : N;
      system_id : N;
      source_time_micro_secs : N;
      scale_code : N;
      reserved_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_indicator record < 256 ^ N.of_nat 2)%N /\
      (closing_price_rule record < 256 ^ N.of_nat 2)%N /\
      (closing_price record < 256 ^ N.of_nat 4)%N /\
      (adjusted_closing_price record < 256 ^ N.of_nat 4)%N /\
      (nb_trades record < 256 ^ N.of_nat 4)%N /\
      (amount_traded record < 256 ^ N.of_nat 8)%N /\
      (qty_shares record < 256 ^ N.of_nat 4)%N /\
      (system_id record < 256 ^ N.of_nat 4)%N /\
      (source_time_micro_secs record < 256 ^ N.of_nat 2)%N /\
      (scale_code record < 256 ^ N.of_nat 1)%N /\
      (reserved_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_seq_num record) ++
      encode_uint 2 (sending_indicator record) ++
      encode_uint 2 (closing_price_rule record) ++
      encode_uint 4 (closing_price record) ++
      encode_uint 4 (adjusted_closing_price record) ++
      encode_uint 4 (nb_trades record) ++
      encode_uint 8 (amount_traded record) ++
      encode_uint 4 (qty_shares record) ++
      encode_uint 4 (system_id record) ++
      encode_uint 2 (source_time_micro_secs record) ++
      encode_uint 1 (scale_code record) ++
      encode_uint 5 (reserved_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_index_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (source_seq_num_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (sending_indicator_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (closing_price_rule_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (closing_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (adjusted_closing_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (nb_trades_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (amount_traded_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (qty_shares_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (system_id_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (source_time_micro_secs_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (scale_code_value, bytes) =>
                                                          match decode_uint 5 bytes with
                                                          | None => None
                                                          | Some (reserved_5_value, bytes) =>
                                                              Some ({| symbol_index := symbol_index_value; source_time := source_time_value; source_seq_num := source_seq_num_value; sending_indicator := sending_indicator_value; closing_price_rule := closing_price_rule_value; closing_price := closing_price_value; adjusted_closing_price := adjusted_closing_price_value; nb_trades := nb_trades_value; amount_traded := amount_traded_value; qty_shares := qty_shares_value; system_id := system_id_value; source_time_micro_secs := source_time_micro_secs_value; scale_code := scale_code_value; reserved_5 := reserved_5_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End VwapClosingPriceMessage.

End WsePricesAndTradesV68.
