From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * SIX Swiss Exchange SIX Swiss Exchange ITCH Market Data Interface Total View

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

Module SixSwissExchangeTotalViewV1240.

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

    (** Timestamp of seconds since midnight, used in combination with the nanoseconds timestamp of each message *)
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

    (** Sent as a result of trade events at the system, group and Orderbook level *)
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

  Module QuantityTickSizeMessage.

    (** Shows the Quantity Tick (Category) of a Security *)
    Record t := {
      timestamp : N;
      quantity_tick_table_id : N;
      quantity_tick_size : N;
      quantity_start : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (quantity_tick_table_id record < 256 ^ N.of_nat 4)%N /\
      (quantity_tick_size record < 256 ^ N.of_nat 4)%N /\
      (quantity_start record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (quantity_tick_table_id record) ++
      encode_uint 4 (quantity_tick_size record) ++
      encode_uint 4 (quantity_start record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (quantity_tick_table_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_tick_size_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_start_value, bytes) =>
                      Some ({| timestamp := timestamp_value; quantity_tick_table_id := quantity_tick_table_id_value; quantity_tick_size := quantity_tick_size_value; quantity_start := quantity_start_value |}, bytes)
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

  End QuantityTickSizeMessage.

  Module PriceTickSizeMessage.

    (** Shows the Price Tick (Category) of a Security *)
    Record t := {
      timestamp : N;
      price_tick_table_id : N;
      price_tick_size : N;
      price_start : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (price_tick_table_id record < 256 ^ N.of_nat 4)%N /\
      (price_tick_size record < 256 ^ N.of_nat 4)%N /\
      (price_start record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (price_tick_table_id record) ++
      encode_uint 4 (price_tick_size record) ++
      encode_uint 4 (price_start record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (price_tick_table_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_tick_size_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_start_value, bytes) =>
                      Some ({| timestamp := timestamp_value; price_tick_table_id := price_tick_table_id_value; price_tick_size := price_tick_size_value; price_start := price_start_value |}, bytes)
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

  Module OrderbookDirectoryMessage.

    (** Provides the basic reference data for the active Orderbooks for a specific OBM partition *)
    Record t := {
      timestamp : N;
      orderbook : N;
      price_type : list byte;
      isin : list byte;
      currency : list byte;
      group : list byte;
      minimum_quantity : N;
      quantity_tick_table_id : N;
      price_tick_table_id : N;
      price_decimals : N;
      delisting_date : N;
      delisting_time : N;
      qod_price_decimals : N;
      security_exchange : list byte;
      reference_exchange : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_type record) = 1 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (group record) = 8 /\
      (minimum_quantity record < 256 ^ N.of_nat 4)%N /\
      (quantity_tick_table_id record < 256 ^ N.of_nat 4)%N /\
      (price_tick_table_id record < 256 ^ N.of_nat 4)%N /\
      (price_decimals record < 256 ^ N.of_nat 4)%N /\
      (delisting_date record < 256 ^ N.of_nat 4)%N /\
      (delisting_time record < 256 ^ N.of_nat 4)%N /\
      (qod_price_decimals record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_exchange record) = 4 /\
      Datatypes.length (reference_exchange record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (price_type record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 8 (group record) ++
      encode_uint 4 (minimum_quantity record) ++
      encode_uint 4 (quantity_tick_table_id record) ++
      encode_uint 4 (price_tick_table_id record) ++
      encode_uint 4 (price_decimals record) ++
      encode_uint 4 (delisting_date record) ++
      encode_uint 4 (delisting_time record) ++
      encode_uint 4 (qod_price_decimals record) ++
      encode_bytes 4 (security_exchange record) ++
      encode_bytes 4 (reference_exchange record).

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
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (currency_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (group_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (minimum_quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (quantity_tick_table_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (price_tick_table_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (price_decimals_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (delisting_date_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (delisting_time_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (qod_price_decimals_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (security_exchange_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (reference_exchange_value, bytes) =>
                                                                  Some ({| timestamp := timestamp_value; orderbook := orderbook_value; price_type := price_type_value; isin := isin_value; currency := currency_value; group := group_value; minimum_quantity := minimum_quantity_value; quantity_tick_table_id := quantity_tick_table_id_value; price_tick_table_id := price_tick_table_id_value; price_decimals := price_decimals_value; delisting_date := delisting_date_value; delisting_time := delisting_time_value; qod_price_decimals := qod_price_decimals_value; security_exchange := security_exchange_value; reference_exchange := reference_exchange_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookDirectoryMessage.

  Module OrderbookTradingActionMessage.

    (** Sent as a result of an Orderbook state or condition change *)
    Record t := {
      timestamp : N;
      orderbook : N;
      trading_state : list byte;
      book_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (book_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (book_condition record).

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
                  | Some (book_condition_value, bytes) =>
                      Some ({| timestamp := timestamp_value; orderbook := orderbook_value; trading_state := trading_state_value; book_condition := book_condition_value |}, bytes)
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

    (** A new order has been accepted and added to the book; an Order Number and Quantity of zero carries the reference price *)
    Record t := {
      timestamp : N;
      order_number : N;
      order_verb : list byte;
      order_quantity : N;
      orderbook : N;
      order_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_verb record) = 1 /\
      (order_quantity record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (order_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_bytes 1 (order_verb record) ++
      encode_uint 4 (order_quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 4 (order_price record).

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
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (orderbook_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_price_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_number := order_number_value; order_verb := order_verb_value; order_quantity := order_quantity_value; orderbook := orderbook_value; order_price := order_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

    (** An order on the book has been executed in whole or in part *)
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
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 4 bytes with
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

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** An order on the book has been executed at a price different from its initial display price *)
    Record t := {
      timestamp : N;
      order_number : N;
      executed_quantity : N;
      match_number : N;
      printable : list byte;
      execution_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (printable record) = 1 /\
      (execution_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (execution_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 4 bytes with
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
                          | Some (execution_price_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; printable := printable_value; execution_price := execution_price_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceMessage.

  Module ExecutionSummaryMessage.

    (** Sent prior to the individual order execution and trade messages for an incoming order that executes in the CLOB or QDM order book *)
    Record t := {
      timestamp : N;
      orderbook : N;
      aggressor_side : list byte;
      total_mpob_quantity : N;
      total_ebbo_book_quantity : N;
      total_clobqdm_quantity : N;
      resting_hidden_quantity : N;
      resting_cancelled_quantity : N;
      far_side : list byte;
      far_price : N;
      far_quantity_remaining : N;
      number_of_executions : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (aggressor_side record) = 1 /\
      (total_mpob_quantity record < 256 ^ N.of_nat 4)%N /\
      (total_ebbo_book_quantity record < 256 ^ N.of_nat 4)%N /\
      (total_clobqdm_quantity record < 256 ^ N.of_nat 4)%N /\
      (resting_hidden_quantity record < 256 ^ N.of_nat 4)%N /\
      (resting_cancelled_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (far_side record) = 1 /\
      (far_price record < 256 ^ N.of_nat 4)%N /\
      (far_quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      (number_of_executions record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (aggressor_side record) ++
      encode_uint 4 (total_mpob_quantity record) ++
      encode_uint 4 (total_ebbo_book_quantity record) ++
      encode_uint 4 (total_clobqdm_quantity record) ++
      encode_uint 4 (resting_hidden_quantity record) ++
      encode_uint 4 (resting_cancelled_quantity record) ++
      encode_bytes 1 (far_side record) ++
      encode_uint 4 (far_price record) ++
      encode_uint 4 (far_quantity_remaining record) ++
      encode_uint 2 (number_of_executions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (aggressor_side_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (total_mpob_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (total_ebbo_book_quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (total_clobqdm_quantity_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (resting_hidden_quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (resting_cancelled_quantity_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (far_side_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (far_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (far_quantity_remaining_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (number_of_executions_value, bytes) =>
                                                      Some ({| timestamp := timestamp_value; orderbook := orderbook_value; aggressor_side := aggressor_side_value; total_mpob_quantity := total_mpob_quantity_value; total_ebbo_book_quantity := total_ebbo_book_quantity_value; total_clobqdm_quantity := total_clobqdm_quantity_value; resting_hidden_quantity := resting_hidden_quantity_value; resting_cancelled_quantity := resting_cancelled_quantity_value; far_side := far_side_value; far_price := far_price_value; far_quantity_remaining := far_quantity_remaining_value; number_of_executions := number_of_executions_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionSummaryMessage.

  Module TradeMessage.

    (** Informs about a trade without pre-trade transparency *)
    Record t := {
      timestamp : N;
      execution_time : N;
      orderbook : N;
      executed_quantity : N;
      execution_price : N;
      match_number : N;
      book_type : list byte;
      trading_session_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (execution_time record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (book_type record) = 1 /\
      Datatypes.length (trading_session_id record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (execution_time record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (execution_price record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (book_type record) ++
      encode_bytes 1 (trading_session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (execution_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (executed_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (execution_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (book_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trading_session_id_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; execution_time := execution_time_value; orderbook := orderbook_value; executed_quantity := executed_quantity_value; execution_price := execution_price_value; match_number := match_number_value; book_type := book_type_value; trading_session_id := trading_session_id_value |}, bytes)
                                  end
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
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module BrokenTradeMessage.

    (** Informs about a SIX Swiss Exchange mistrade decision *)
    Record t := {
      timestamp : N;
      match_number : N;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (match_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reason_value, bytes) =>
                  Some ({| timestamp := timestamp_value; match_number := match_number_value; reason := reason_value |}, bytes)
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

    (** Sent whenever an order on the Orderbook is being cancelled *)
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

    (** Sent whenever an order on the Orderbook has been cancel-replaced *)
    Record t := {
      timestamp : N;
      original_order_number : N;
      new_order_number : N;
      order_quantity : N;
      order_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (original_order_number record < 256 ^ N.of_nat 8)%N /\
      (new_order_number record < 256 ^ N.of_nat 8)%N /\
      (order_quantity record < 256 ^ N.of_nat 4)%N /\
      (order_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (original_order_number record) ++
      encode_uint 8 (new_order_number record) ++
      encode_uint 4 (order_quantity record) ++
      encode_uint 4 (order_price record).

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
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_price_value, bytes) =>
                          Some ({| timestamp := timestamp_value; original_order_number := original_order_number_value; new_order_number := new_order_number_value; order_quantity := order_quantity_value; order_price := order_price_value |}, bytes)
                      end
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

    (** Sent during non-automatic matching periods telling the users what would happen if the book was uncrossed now *)
    Record t := {
      timestamp : N;
      theoretical_opening_quantity : N;
      orderbook : N;
      best_bid : N;
      best_offer : N;
      theoretical_opening_price : N;
      cross_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (theoretical_opening_quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (best_bid record < 256 ^ N.of_nat 4)%N /\
      (best_offer record < 256 ^ N.of_nat 4)%N /\
      (theoretical_opening_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (theoretical_opening_quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 4 (best_bid record) ++
      encode_uint 4 (best_offer record) ++
      encode_uint 4 (theoretical_opening_price record) ++
      encode_bytes 1 (cross_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (theoretical_opening_quantity_value, bytes) =>
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
                          | Some (theoretical_opening_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cross_type_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; theoretical_opening_quantity := theoretical_opening_quantity_value; orderbook := orderbook_value; best_bid := best_bid_value; best_offer := best_offer_value; theoretical_opening_price := theoretical_opening_price_value; cross_type := cross_type_value |}, bytes)
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

End SixSwissExchangeTotalViewV1240.
