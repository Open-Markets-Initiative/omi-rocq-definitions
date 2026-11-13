From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Philippine Stock Exchange Pse Equities Itch Total View

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

Module PseEquitiesTotalViewV23.

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

  Module TimeStampSecondsMessage.

    (** Time Stamp - Seconds Message. *)
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

  End TimeStampSecondsMessage.

  Module SystemEventMessage.

    (** System Event Message. *)
    Record t := {
      timestamp : N;
      group : list byte;
      event_code : list byte;
      orderbook : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (group record) = 8 /\
      Datatypes.length (event_code record) = 1 /\
      (orderbook record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_bytes 8 (group record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 4 (orderbook record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (orderbook_value, bytes) =>
                      Some ({| timestamp := timestamp_value; group := group_value; event_code := event_code_value; orderbook := orderbook_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module TradingScheduleMessage.

    (** Trading Schedule Message. *)
    Record t := {
      timestamp : N;
      group : list byte;
      event_code : list byte;
      orderbook : N;
      scheduled_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (group record) = 8 /\
      Datatypes.length (event_code record) = 1 /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (scheduled_time record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_bytes 8 (group record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 4 (scheduled_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (orderbook_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (scheduled_time_value, bytes) =>
                          Some ({| timestamp := timestamp_value; group := group_value; event_code := event_code_value; orderbook := orderbook_value; scheduled_time := scheduled_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingScheduleMessage.

  Module PriceTickSizeMessage.

    (** Tick Size Table. *)
    Record t := {
      timestamp : N;
      tick_size_table_id : N;
      tick_size_integer_4 : N;
      price_start : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (tick_size_integer_4 record < 256 ^ N.of_nat 4)%N /\
      (price_start record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (tick_size_table_id record) ++
      encode_uint 4 (tick_size_integer_4 record) ++
      encode_uint 4 (price_start record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (tick_size_table_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tick_size_integer_4_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_start_value, bytes) =>
                      Some ({| timestamp := timestamp_value; tick_size_table_id := tick_size_table_id_value; tick_size_integer_4 := tick_size_integer_4_value; price_start := price_start_value |}, bytes)
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

  End PriceTickSizeMessage.

  Module QuantityTickSizeMessage.

    (** Tick Size Table. *)
    Record t := {
      timestamp : N;
      tick_size_table_id : N;
      tick_size_integer_8 : N;
      quantity_start : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (tick_size_integer_8 record < 256 ^ N.of_nat 8)%N /\
      (quantity_start record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (tick_size_table_id record) ++
      encode_uint 8 (tick_size_integer_8 record) ++
      encode_uint 8 (quantity_start record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (tick_size_table_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tick_size_integer_8_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_start_value, bytes) =>
                      Some ({| timestamp := timestamp_value; tick_size_table_id := tick_size_table_id_value; tick_size_integer_8 := tick_size_integer_8_value; quantity_start := quantity_start_value |}, bytes)
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

  End QuantityTickSizeMessage.

  Module OrderbookDirectoryMessage.

    (** Orderbook Directory Message. *)
    Record t := {
      timestamp : N;
      orderbook : N;
      price_type : list byte;
      isin : list byte;
      sec_code : list byte;
      currency : list byte;
      group : list byte;
      lot_size : N;
      quantity_tick_size_table_id : N;
      price_tick_size_table_id : N;
      price_decimals : N;
      delisting_date : N;
      delisting_time : N;
      instrument_type : list byte;
      shares : N;
      product_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (sec_code record) = 12 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (group record) = 8 /\
      (lot_size record < 256 ^ N.of_nat 8)%N /\
      (quantity_tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (price_tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (price_decimals record < 256 ^ N.of_nat 4)%N /\
      (delisting_date record < 256 ^ N.of_nat 4)%N /\
      (delisting_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (instrument_type record) = 1 /\
      (shares record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (product_code record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 12 (sec_code record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 8 (group record) ++
      encode_uint 8 (lot_size record) ++
      encode_uint 4 (quantity_tick_size_table_id record) ++
      encode_uint 4 (price_tick_size_table_id record) ++
      encode_uint 4 (price_decimals record) ++
      encode_uint 4 (delisting_date record) ++
      encode_uint 4 (delisting_time record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_uint 8 (shares record) ++
      encode_bytes 8 (product_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (price_type_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (sec_code_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (currency_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (group_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (lot_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (quantity_tick_size_table_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (price_tick_size_table_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (price_decimals_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (delisting_date_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (delisting_time_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (instrument_type_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (shares_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (product_code_value, bytes) =>
                                                                      Some ({| timestamp := timestamp_value; orderbook := orderbook_value; price_type := price_type_value; isin := isin_value; sec_code := sec_code_value; currency := currency_value; group := group_value; lot_size := lot_size_value; quantity_tick_size_table_id := quantity_tick_size_table_id_value; price_tick_size_table_id := price_tick_size_table_id_value; price_decimals := price_decimals_value; delisting_date := delisting_date_value; delisting_time := delisting_time_value; instrument_type := instrument_type_value; shares := shares_value; product_code := product_code_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 89.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookDirectoryMessage.

  Module OrderbookRestrictionsMessage.

    (** Orderbook Restrictions Message. *)
    Record t := {
      timestamp : N;
      orderbook : N;
      short_sell_eligible : list byte;
      high_collar : N;
      low_collar : N;
      cb_limit_up : N;
      cb_limit_down : N;
      cb_limit_decimals : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (short_sell_eligible record) = 1 /\
      (high_collar record < 256 ^ N.of_nat 4)%N /\
      (low_collar record < 256 ^ N.of_nat 4)%N /\
      (cb_limit_up record < 256 ^ N.of_nat 4)%N /\
      (cb_limit_down record < 256 ^ N.of_nat 4)%N /\
      (cb_limit_decimals record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (short_sell_eligible record) ++
      encode_uint 4 (high_collar record) ++
      encode_uint 4 (low_collar record) ++
      encode_uint 4 (cb_limit_up record) ++
      encode_uint 4 (cb_limit_down record) ++
      encode_uint 4 (cb_limit_decimals record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (short_sell_eligible_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (high_collar_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (low_collar_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (cb_limit_up_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (cb_limit_down_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cb_limit_decimals_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; orderbook := orderbook_value; short_sell_eligible := short_sell_eligible_value; high_collar := high_collar_value; low_collar := low_collar_value; cb_limit_up := cb_limit_up_value; cb_limit_down := cb_limit_down_value; cb_limit_decimals := cb_limit_decimals_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookRestrictionsMessage.

  Module OrderbookTradingActionMessage.

    (** Stock Trading Action Message. *)
    Record t := {
      timestamp : N;
      orderbook : N;
      trading_state : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_state_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      Some ({| timestamp := timestamp_value; orderbook := orderbook_value; trading_state := trading_state_value; reason := reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End OrderbookTradingActionMessage.

  Module AddOrderMessage.

    (** Add Order Message. *)
    Record t := {
      timestamp : N;
      order_number : N;
      order_verb : list byte;
      quantity : N;
      orderbook : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_verb record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_bytes 1 (order_verb record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_verb_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (orderbook_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_number := order_number_value; order_verb := order_verb_value; quantity := quantity_value; orderbook := orderbook_value; price := price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module OrderExecutedMessage.

    (** Order Executed Message. *)
    Record t := {
      timestamp : N;
      order_number : N;
      executed_quantity : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      Some ({| timestamp := timestamp_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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

  End OrderExecutedMessage.

  Module OrderExecutedWithBrokerIdMessage.

    (** Order Executed (with Broker ID) Message. *)
    Record t := {
      timestamp : N;
      order_number : N;
      executed_quantity : N;
      match_number : N;
      passive_broker_id : list byte;
      active_broker_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (passive_broker_id record) = 4 /\
      Datatypes.length (active_broker_id record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 4 (passive_broker_id record) ++
      encode_bytes 4 (active_broker_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (passive_broker_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (active_broker_id_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; passive_broker_id := passive_broker_id_value; active_broker_id := active_broker_id_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithBrokerIdMessage.

  Module OrderExecutedWithPriceMessage.

    (** Order Executed with Price Message. *)
    Record t := {
      timestamp : N;
      order_number : N;
      executed_quantity : N;
      match_number : N;
      printable : list byte;
      order_execution_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (printable record) = 1 /\
      (order_execution_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (order_execution_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (printable_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_execution_price_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; printable := printable_value; order_execution_price := order_execution_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceMessage.

  Module OrderExecutedWithPriceAndBrokerIdMessage.

    (** Order Executed with Price (and Broker ID) Message. *)
    Record t := {
      timestamp : N;
      order_number : N;
      executed_quantity : N;
      match_number : N;
      printable : list byte;
      order_execution_price : N;
      passive_broker_id : list byte;
      active_broker_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (printable record) = 1 /\
      (order_execution_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (passive_broker_id record) = 4 /\
      Datatypes.length (active_broker_id record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (order_execution_price record) ++
      encode_bytes 4 (passive_broker_id record) ++
      encode_bytes 4 (active_broker_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (printable_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_execution_price_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (passive_broker_id_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (active_broker_id_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; printable := printable_value; order_execution_price := order_execution_price_value; passive_broker_id := passive_broker_id_value; active_broker_id := active_broker_id_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceAndBrokerIdMessage.

  Module BrokenTradeMessage.

    (** Broken Trade Message. *)
    Record t := {
      timestamp : N;
      match_number : N;
      broken_trade_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broken_trade_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (broken_trade_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (match_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (broken_trade_reason_value, bytes) =>
                  Some ({| timestamp := timestamp_value; match_number := match_number_value; broken_trade_reason := broken_trade_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End BrokenTradeMessage.

  Module OrderDeleteMessage.

    (** Order Delete Message. *)
    Record t := {
      timestamp : N;
      order_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              Some ({| timestamp := timestamp_value; order_number := order_number_value |}, bytes)
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

  End OrderDeleteMessage.

  Module OrderReplaceMessage.

    (** Order Replace Message. *)
    Record t := {
      timestamp : N;
      original_order_number : N;
      new_order_number : N;
      quantity : N;
      replace_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (original_order_number record < 256 ^ N.of_nat 8)%N /\
      (new_order_number record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (replace_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (original_order_number record) ++
      encode_uint 8 (new_order_number record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (replace_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (original_order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (new_order_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (replace_price_value, bytes) =>
                          Some ({| timestamp := timestamp_value; original_order_number := original_order_number_value; new_order_number := new_order_number_value; quantity := quantity_value; replace_price := replace_price_value |}, bytes)
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

  End OrderReplaceMessage.

  Module IndicativePriceQuantityMessage.

    (** Indicative Price/Quantity Message. *)
    Record t := {
      timestamp : N;
      theoretical_auction_quantity : N;
      orderbook : N;
      best_bid : N;
      best_offer : N;
      theoretical_auction_price : N;
      auction_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (theoretical_auction_quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (best_bid record < 256 ^ N.of_nat 4)%N /\
      (best_offer record < 256 ^ N.of_nat 4)%N /\
      (theoretical_auction_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (theoretical_auction_quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 4 (best_bid record) ++
      encode_uint 4 (best_offer record) ++
      encode_uint 4 (theoretical_auction_price record) ++
      encode_bytes 1 (auction_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (theoretical_auction_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (best_bid_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (best_offer_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (theoretical_auction_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (auction_type_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; theoretical_auction_quantity := theoretical_auction_quantity_value; orderbook := orderbook_value; best_bid := best_bid_value; best_offer := best_offer_value; theoretical_auction_price := theoretical_auction_price_value; auction_type := auction_type_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndicativePriceQuantityMessage.

  Module TradeMessage.

    (** Trade Message. *)
    Record t := {
      timestamp : N;
      executed_quantity : N;
      orderbook : N;
      printable : list byte;
      execution_price : N;
      match_number : N;
      trade_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (printable record) = 1 /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (execution_price record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (trade_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (printable_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (execution_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_indicator_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; executed_quantity := executed_quantity_value; orderbook := orderbook_value; printable := printable_value; execution_price := execution_price_value; match_number := match_number_value; trade_indicator := trade_indicator_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module TradeWithBrokerIdMessage.

    (** Trade (with Broker ID) Message. *)
    Record t := {
      timestamp : N;
      executed_quantity : N;
      orderbook : N;
      printable : list byte;
      execution_price : N;
      match_number : N;
      trade_indicator : list byte;
      buy_broker_id : list byte;
      sell_broker_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (printable record) = 1 /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_indicator record) = 1 /\
      Datatypes.length (buy_broker_id record) = 4 /\
      Datatypes.length (sell_broker_id record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (execution_price record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (trade_indicator record) ++
      encode_bytes 4 (buy_broker_id record) ++
      encode_bytes 4 (sell_broker_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (printable_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (execution_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_indicator_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (buy_broker_id_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (sell_broker_id_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; executed_quantity := executed_quantity_value; orderbook := orderbook_value; printable := printable_value; execution_price := execution_price_value; match_number := match_number_value; trade_indicator := trade_indicator_value; buy_broker_id := buy_broker_id_value; sell_broker_id := sell_broker_id_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeWithBrokerIdMessage.

  Module ForeignSharesAvailableMessage.

    (** Foreign Shares Available Message. *)
    Record t := {
      timestamp : N;
      product_code : list byte;
      ownership_rule_id : list byte;
      sign : list byte;
      foreign_shares_available : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (product_code record) = 8 /\
      Datatypes.length (ownership_rule_id record) = 2 /\
      Datatypes.length (sign record) = 1 /\
      (foreign_shares_available record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_bytes 8 (product_code record) ++
      encode_bytes 2 (ownership_rule_id record) ++
      encode_bytes 1 (sign record) ++
      encode_uint 8 (foreign_shares_available record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (product_code_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (ownership_rule_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sign_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (foreign_shares_available_value, bytes) =>
                          Some ({| timestamp := timestamp_value; product_code := product_code_value; ownership_rule_id := ownership_rule_id_value; sign := sign_value; foreign_shares_available := foreign_shares_available_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ForeignSharesAvailableMessage.

End PseEquitiesTotalViewV23.
