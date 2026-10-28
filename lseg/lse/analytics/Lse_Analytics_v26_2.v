From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * London Stock Exchange Analytics

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
      - a run counted by a field
      - a field read in bits
  *)

Module LseAnalyticsV262.

  Module UnitHeader.

    Record t := {
      length_ : N;
      message_count : N;
      market_data_group : list byte;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_data_group record) = 1 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_bytes 1 (market_data_group record) ++
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; market_data_group := market_data_group_value; sequence_number := sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnitHeader.

  Module MessageHeader.

    (** Gtp Udp Message Header *)
    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  Module SystemEventMessage.

    (** Sent to indicate the start and end of the day. *)
    Record t := {
      timestamp : N;
      event_code : list byte;
      source_venue : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1 /\
      (source_venue record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 2 (source_venue record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  Some ({| timestamp := timestamp_value; event_code := event_code_value; source_venue := source_venue_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module InstrumentStatusMessage.

    (** Used to communicate scheduled and unscheduled session changes. When sent in the recovery channel, used to indicate the current trading status of an instrument. *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      trading_status : list byte;
      session_change_reason : N;
      new_end_time : list byte;
      order_book_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (trading_status record) = 1 /\
      (session_change_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (new_end_time record) = 6 /\
      (order_book_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_bytes 1 (trading_status record) ++
      encode_uint 1 (session_change_reason record) ++
      encode_bytes 6 (new_end_time record) ++
      encode_uint 1 (order_book_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (session_change_reason_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (new_end_time_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_book_type_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; trading_status := trading_status_value; session_change_reason := session_change_reason_value; new_end_time := new_end_time_value; order_book_type := order_book_type_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentStatusMessage.

  Module AnalyticsMessage.

    (** Analytics Message is used to disseminate additional statistics including order book activity statistics. *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      start_time : N;
      end_time : N;
      buy_order_count : N;
      sell_order_count : N;
      buy_order_size : N;
      sell_order_size : N;
      buy_order_cancellations : N;
      sell_order_cancellations : N;
      buy_limit_order_cancellations : N;
      buy_market_order_cancellations : N;
      sell_limit_order_cancellations : N;
      sell_market_order_cancellations : N;
      bid_ask_spread : N;
      vwap_buy : N;
      vwap_sell : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (start_time record < 256 ^ N.of_nat 8)%N /\
      (end_time record < 256 ^ N.of_nat 8)%N /\
      (buy_order_count record < 256 ^ N.of_nat 4)%N /\
      (sell_order_count record < 256 ^ N.of_nat 4)%N /\
      (buy_order_size record < 256 ^ N.of_nat 8)%N /\
      (sell_order_size record < 256 ^ N.of_nat 8)%N /\
      (buy_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (sell_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (buy_limit_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (buy_market_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (sell_limit_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (sell_market_order_cancellations record < 256 ^ N.of_nat 4)%N /\
      (bid_ask_spread record < 256 ^ N.of_nat 8)%N /\
      (vwap_buy record < 256 ^ N.of_nat 8)%N /\
      (vwap_sell record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (start_time record) ++
      encode_uint 8 (end_time record) ++
      encode_uint 4 (buy_order_count record) ++
      encode_uint 4 (sell_order_count record) ++
      encode_uint 8 (buy_order_size record) ++
      encode_uint 8 (sell_order_size record) ++
      encode_uint 4 (buy_order_cancellations record) ++
      encode_uint 4 (sell_order_cancellations record) ++
      encode_uint 4 (buy_limit_order_cancellations record) ++
      encode_uint 4 (buy_market_order_cancellations record) ++
      encode_uint 4 (sell_limit_order_cancellations record) ++
      encode_uint 4 (sell_market_order_cancellations record) ++
      encode_uint 8 (bid_ask_spread record) ++
      encode_uint 8 (vwap_buy record) ++
      encode_uint 8 (vwap_sell record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (start_time_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (end_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (buy_order_count_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (sell_order_count_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (buy_order_size_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (sell_order_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (buy_order_cancellations_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (sell_order_cancellations_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (buy_limit_order_cancellations_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (buy_market_order_cancellations_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (sell_limit_order_cancellations_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (sell_market_order_cancellations_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (bid_ask_spread_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (vwap_buy_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (vwap_sell_value, bytes) =>
                                                                              Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; start_time := start_time_value; end_time := end_time_value; buy_order_count := buy_order_count_value; sell_order_count := sell_order_count_value; buy_order_size := buy_order_size_value; sell_order_size := sell_order_size_value; buy_order_cancellations := buy_order_cancellations_value; sell_order_cancellations := sell_order_cancellations_value; buy_limit_order_cancellations := buy_limit_order_cancellations_value; buy_market_order_cancellations := buy_market_order_cancellations_value; sell_limit_order_cancellations := sell_limit_order_cancellations_value; sell_market_order_cancellations := sell_market_order_cancellations_value; bid_ask_spread := bid_ask_spread_value; vwap_buy := vwap_buy_value; vwap_sell := vwap_sell_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 106.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AnalyticsMessage.

End LseAnalyticsV262.
