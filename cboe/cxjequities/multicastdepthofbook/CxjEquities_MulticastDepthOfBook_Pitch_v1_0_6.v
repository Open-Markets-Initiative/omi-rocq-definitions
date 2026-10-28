From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Multicast Depth Of Book

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
      - a run filling what frames it
      - a field read in bits
  *)

Module CxjEquitiesMulticastDepthOfBookV106.

  Module PacketHeader.

    Record t := {
      length_ : N;
      message_count : N;
      unit_ : N;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (unit_ record < 256 ^ N.of_nat 1)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 1 (unit_ record) ++
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (unit__value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; unit_ := unit__value; sequence := sequence_value |}, bytes)
                  end
              end
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

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 1)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  Module UnitClearMessage.

    (** Instructs feed recipients to clear all orders for the Cboe Japan book in the unit specified in the Sequenced Unit Header. It would be distributed in rare recovery events such as a datacenter fail-over. *)
    Record t := {
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (reserved_4_value, bytes) =>
          Some ({| reserved_4 := reserved_4_value |}, bytes)
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

  End UnitClearMessage.

  Module AddOrderMessage.

    (** Represents a newly accepted order on the Cboe Japan book. It includes a day-specific Order Id assigned by Cboe Japan to the order. *)
    Record t := {
      timestamp : N;
      order_id : N;
      side_indicator : list byte;
      quantity : N;
      symbol : list byte;
      price : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 8 (price record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reserved_1_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity := quantity_value; symbol := symbol_value; price := price_value; reserved_1 := reserved_1_value |}, bytes)
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module OrderExecutedMessage.

    (** Sent when a visible order on the Cboe Japan book is executed in whole or in part. The execution price equals the order price found in the original Add Order message or the order price in the latest Modify Order message referencing the Order Id. *)
    Record t := {
      timestamp : N;
      order_id : N;
      executed_quantity : N;
      execution_id : N;
      contra_order_id : N;
      tick_direction : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      (contra_order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick_direction record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (execution_id record) ++
      encode_uint 8 (contra_order_id record) ++
      encode_bytes 1 (tick_direction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (execution_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (contra_order_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (tick_direction_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_id := order_id_value; executed_quantity := executed_quantity_value; execution_id := execution_id_value; contra_order_id := contra_order_id_value; tick_direction := tick_direction_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module ReduceSizeMessage.

    (** Sent when a visible order on the Cboe Japan book is partially reduced. *)
    Record t := {
      timestamp : N;
      order_id : N;
      cancelled_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (cancelled_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (cancelled_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (cancelled_quantity_value, bytes) =>
                  Some ({| timestamp := timestamp_value; order_id := order_id_value; cancelled_quantity := cancelled_quantity_value |}, bytes)
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

  End ReduceSizeMessage.

  Module ModifyOrderMessage.

    (** Sent whenever an open order is visibly modified. The Order Id refers to the Order Id of the original Add Order message. *)
    Record t := {
      timestamp : N;
      order_id : N;
      quantity : N;
      price : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          Some ({| timestamp := timestamp_value; order_id := order_id_value; quantity := quantity_value; price := price_value; reserved_1 := reserved_1_value |}, bytes)
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

  End ModifyOrderMessage.

  Module DeleteOrderMessage.

    (** Sent whenever a booked order is cancelled or leaves the order book. The Order Id refers to the Order Id of the original Add Order message. *)
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

  End DeleteOrderMessage.

  Module TradeMessage.

    (** Sent when there is an execution against any non-displayed portion of an iceberg order. Trade messages do not alter the book and can be ignored if messages are being used solely to build a book. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      quantity : N;
      price : N;
      execution_id : N;
      order_id : N;
      contra_order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (contra_order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (execution_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (contra_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (execution_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (contra_order_id_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; symbol := symbol_value; quantity := quantity_value; price := price_value; execution_id := execution_id_value; order_id := order_id_value; contra_order_id := contra_order_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module TradeBreakMessage.

    (** Sent whenever an execution on Cboe Japan is cancelled. *)
    Record t := {
      timestamp : N;
      execution_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (execution_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (execution_id_value, bytes) =>
              Some ({| timestamp := timestamp_value; execution_id := execution_id_value |}, bytes)
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

  End TradeBreakMessage.

  Module EndOfSessionMessage.

    (** Sent for each unit when the unit shuts down. No additional sequenced messages will be delivered for this unit, but heartbeats from the unit may be received. *)
    Record t := {
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (reserved_4_value, bytes) =>
          Some ({| reserved_4 := reserved_4_value |}, bytes)
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

  End EndOfSessionMessage.

End CxjEquitiesMulticastDepthOfBookV106.
