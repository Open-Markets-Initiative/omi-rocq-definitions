From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * CIX Trading Inc. CIX Market Data Feed

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
  *)

Module CixAtsCixAspenMarketDataFeedV14.

  Module PacketHeader.

    Record t := {
      market_day_identifier : list byte;
      feed_identifier : list byte;
      sequence : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_day_identifier record) = 9 /\
      Datatypes.length (feed_identifier record) = 1 /\
      (sequence record < 256 ^ N.of_nat 8)%N /\
      (count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (market_day_identifier record) ++
      encode_bytes 1 (feed_identifier record) ++
      encode_uint 8 (sequence record) ++
      encode_uint 2 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (market_day_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (feed_identifier_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sequence_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (count_value, bytes) =>
                      Some ({| market_day_identifier := market_day_identifier_value; feed_identifier := feed_identifier_value; sequence := sequence_value; count := count_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module MessageHeader.

    (** Length of the message *)
    Record t := {
      length_ : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| length_ := length__value; message_type := message_type_value |}, bytes)
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

  Module MarketEventMessage.

    (** Transitions in the overall session state *)
    Record t := {
      reserved_2 : list byte;
      timestamp : N;
      event : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_value, bytes) =>
                  Some ({| reserved_2 := reserved_2_value; timestamp := timestamp_value; event := event_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketEventMessage.

  Module SymbolInformationMessage.

    (** Reference data for each symbol that may be traded *)
    Record t := {
      timestamp : N;
      symbol_id : N;
      symbol : list byte;
      listing_market : list byte;
      board_lot_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (listing_market record) = 1 /\
      (board_lot_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (symbol_id record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 1 (listing_market record) ++
      encode_uint 4 (board_lot_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (listing_market_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (board_lot_size_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol_id := symbol_id_value; symbol := symbol_value; listing_market := listing_market_value; board_lot_size := board_lot_size_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolInformationMessage.

  Module SymbolStateMessage.

    (** Individual symbol trading state (halts) *)
    Record t := {
      timestamp : N;
      symbol_id : N;
      symbol : list byte;
      state : list byte;
      reserved_1 : list byte;
      info : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 11 /\
      Datatypes.length (state record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (info record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (symbol_id record) ++
      encode_bytes 11 (symbol record) ++
      encode_bytes 1 (state record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 4 (info record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (state_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (info_value, bytes) =>
                              Some ({| timestamp := timestamp_value; symbol_id := symbol_id_value; symbol := symbol_value; state := state_value; reserved_1 := reserved_1_value; info := info_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolStateMessage.

  Module NewOrderAddMessage.

    (** A new resting order added to the book *)
    Record t := {
      timestamp : N;
      symbol_id : N;
      order_id : N;
      side : list byte;
      quantity : N;
      symbol : list byte;
      price : N;
      broker : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (symbol_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (quantity record) ++
      encode_bytes 11 (symbol record) ++
      encode_uint 8 (price record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (broker_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (reserved_1_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; symbol_id := symbol_id_value; order_id := order_id_value; side := side_value; quantity := quantity_value; symbol := symbol_value; price := price_value; broker := broker_value; reserved_1 := reserved_1_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderAddMessage.

  Module OrderPartialCancelMessage.

    (** Part of a resting order is canceled *)
    Record t := {
      timestamp : N;
      order_id : N;
      quantity_canceled : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_canceled record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (quantity_canceled record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_canceled_value, bytes) =>
                  Some ({| timestamp := timestamp_value; order_id := order_id_value; quantity_canceled := quantity_canceled_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderPartialCancelMessage.

  Module OrderCancelAllMessage.

    (** Sent when the order is canceled in its entirety *)
    Record t := {
      timestamp : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              Some ({| timestamp := timestamp_value; order_id := order_id_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderCancelAllMessage.

  Module OrderExecutedMessage.

    (** Sent when an order is executed *)
    Record t := {
      timestamp : N;
      order_id : N;
      quantity : N;
      execution_id : N;
      side : list byte;
      price : N;
      broker : list byte;
      contra_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 8 (execution_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (execution_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (broker_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (contra_broker_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; order_id := order_id_value; quantity := quantity_value; execution_id := execution_id_value; side := side_value; price := price_value; broker := broker_value; contra_broker := contra_broker_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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

  End OrderExecutedMessage.

  Module TradeMessage.

    (** Sent when a hidden order is executed *)
    Record t := {
      symbol_id : N;
      timestamp : N;
      reserved_8 : N;
      side : list byte;
      shares : N;
      symbol : list byte;
      price : N;
      execution_id : N;
      broker : list byte;
      contra_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      (shares record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (symbol_id record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (shares record) ++
      encode_bytes 11 (symbol record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (execution_id record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (symbol_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (reserved_8_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (shares_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (execution_id_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (broker_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (contra_broker_value, bytes) =>
                                              Some ({| symbol_id := symbol_id_value; timestamp := timestamp_value; reserved_8 := reserved_8_value; side := side_value; shares := shares_value; symbol := symbol_value; price := price_value; execution_id := execution_id_value; broker := broker_value; contra_broker := contra_broker_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module TradeCancelMessage.

    (** Sent whenever an execution on CIX ATS is cancelled *)
    Record t := {
      symbol_id : N;
      timestamp : N;
      reserved_8 : N;
      reserved_1 : list byte;
      shares : N;
      symbol : list byte;
      price : N;
      execution_id : N;
      broker : list byte;
      contra_broker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_1 record) = 1 /\
      (shares record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 11 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (symbol_id record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_uint 8 (shares record) ++
      encode_bytes 11 (symbol record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (execution_id record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (symbol_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (reserved_8_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (shares_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (execution_id_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (broker_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (contra_broker_value, bytes) =>
                                              Some ({| symbol_id := symbol_id_value; timestamp := timestamp_value; reserved_8 := reserved_8_value; reserved_1 := reserved_1_value; shares := shares_value; symbol := symbol_value; price := price_value; execution_id := execution_id_value; broker := broker_value; contra_broker := contra_broker_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelMessage.

  Module TradeCorrectMessage.

    (** Sent whenever an execution on CIX ATS is amended *)
    Record t := {
      symbol_id : N;
      timestamp : N;
      reserved_8 : N;
      reserved_1 : list byte;
      symbol : list byte;
      execution_id : N;
      broker : list byte;
      contra_broker : list byte;
      original_execution_id : N;
      original_trade_price : N;
      original_trade_quantity : N;
      corrected_trade_price : N;
      corrected_trade_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (symbol record) = 11 /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (broker record) = 3 /\
      Datatypes.length (contra_broker record) = 3 /\
      (original_execution_id record < 256 ^ N.of_nat 8)%N /\
      (original_trade_price record < 256 ^ N.of_nat 8)%N /\
      (original_trade_quantity record < 256 ^ N.of_nat 8)%N /\
      (corrected_trade_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_trade_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (symbol_id record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 11 (symbol record) ++
      encode_uint 8 (execution_id record) ++
      encode_bytes 3 (broker record) ++
      encode_bytes 3 (contra_broker record) ++
      encode_uint 8 (original_execution_id record) ++
      encode_uint 8 (original_trade_price record) ++
      encode_uint 8 (original_trade_quantity record) ++
      encode_uint 8 (corrected_trade_price record) ++
      encode_uint 8 (corrected_trade_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (symbol_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (reserved_8_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (execution_id_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (broker_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (contra_broker_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (original_execution_id_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (original_trade_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (original_trade_quantity_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (corrected_trade_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (corrected_trade_quantity_value, bytes) =>
                                                          Some ({| symbol_id := symbol_id_value; timestamp := timestamp_value; reserved_8 := reserved_8_value; reserved_1 := reserved_1_value; symbol := symbol_value; execution_id := execution_id_value; broker := broker_value; contra_broker := contra_broker_value; original_execution_id := original_execution_id_value; original_trade_price := original_trade_price_value; original_trade_quantity := original_trade_quantity_value; corrected_trade_price := corrected_trade_price_value; corrected_trade_quantity := corrected_trade_quantity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 84.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectMessage.

End CixAtsCixAspenMarketDataFeedV14.
