From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Tcp Depth Of Book

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
      - the dispatch that chooses a message by its type
      - a length prefix framing what follows
  *)

Module BxeEquitiesTcpDepthOfBookV434.

  Module DebugPacket.

    (** Debug packets are intended to provide human readable text that may aid in debugging problems. *)
    Record t := {
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (text record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (text_value, bytes) =>
          Some ({| text := text_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End DebugPacket.

  Module LoginAcceptedPacket.

    (** The Soup 2.0 server sends a Login Accepted Packet in response to receiving a valid Login Request  from the client. *)
    Record t := {
      session : list byte;
      sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      Datatypes.length (sequence_number record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_bytes 10 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              Some ({| session := session_value; sequence_number := sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginAcceptedPacket.

  Module LoginRejectedPacket.

    (** The Soup 2.0 server sends this packet in response to an invalid Login Request Packet from the client. *)
    Record t := {
      reject_reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reject_reason_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reject_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reject_reason_code_value, bytes) =>
          Some ({| reject_reason_code := reject_reason_code_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End LoginRejectedPacket.

  Module SequencedMessageHeader.

    (** Cboe Europe ASCII Soup sequenced message header (microsecond timestamp) *)
    Record t := {
      timestamp : list byte;
      sequenced_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (timestamp record) = 11 /\
      Datatypes.length (sequenced_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (timestamp record) ++
      encode_bytes 1 (sequenced_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sequenced_message_type_value, bytes) =>
              Some ({| timestamp := timestamp_value; sequenced_message_type := sequenced_message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SequencedMessageHeader.

  Module SymbolClearMessage.

    (** Instructs feed recipients to clear all orders for the Cboe book in the specified symbol; sent in recovery events such as a data centre fail-over. *)
    Record t := {
      symbol_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          Some ({| symbol_long := symbol_long_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End SymbolClearMessage.

  Module AddOrderMessage.

    (** Represents a newly accepted visible order on the Cboe book with a day-specific Order ID. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_short : list byte;
      symbol_short : list byte;
      price_short : list byte;
      display : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_short record) = 6 /\
      Datatypes.length (symbol_short record) = 6 /\
      Datatypes.length (price_short record) = 10 /\
      Datatypes.length (display record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 6 (shares_short record) ++
      encode_bytes 6 (symbol_short record) ++
      encode_bytes 10 (price_short record) ++
      encode_bytes 1 (display record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_indicator_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_short_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (symbol_short_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (display_value, bytes) =>
                              Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; symbol_short := symbol_short_value; price_short := price_short_value; display := display_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module AddOrderMessageLongForm.

    (** Cboe European platform only. As Add Order Message but with longer Shares, Symbol and Price fields. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_long : list byte;
      symbol_long : list byte;
      price_long : list byte;
      display : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_long record) = 10 /\
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (price_long record) = 19 /\
      Datatypes.length (display record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 10 (shares_long record) ++
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 19 (price_long record) ++
      encode_bytes 1 (display record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_indicator_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (shares_long_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (symbol_long_value, bytes) =>
                      match decode_bytes 19 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (display_value, bytes) =>
                              Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_long := shares_long_value; symbol_long := symbol_long_value; price_long := price_long_value; display := display_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessageLongForm.

  Module OrderExecutedMessage.

    (** Sent when a visible order on the Cboe book is executed in whole or in part at the original Add Order price. *)
    Record t := {
      order_id : list byte;
      executed_shares_short : list byte;
      execution_id : list byte;
      execution_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (executed_shares_short record) = 6 /\
      Datatypes.length (execution_id record) = 12 /\
      Datatypes.length (execution_flag record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 6 (executed_shares_short record) ++
      encode_bytes 12 (execution_id record) ++
      encode_bytes 4 (execution_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (executed_shares_short_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (execution_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (execution_flag_value, bytes) =>
                      Some ({| order_id := order_id_value; executed_shares_short := executed_shares_short_value; execution_id := execution_id_value; execution_flag := execution_flag_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedMessageLongForm.

    (** Cboe European platform only. As Order Executed Message but with a longer Executed Shares field. *)
    Record t := {
      order_id : list byte;
      executed_shares_long : list byte;
      execution_id : list byte;
      execution_flags : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (executed_shares_long record) = 10 /\
      Datatypes.length (execution_id record) = 12 /\
      Datatypes.length (execution_flags record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 10 (executed_shares_long record) ++
      encode_bytes 12 (execution_id record) ++
      encode_bytes 4 (execution_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (executed_shares_long_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (execution_id_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (execution_flags_value, bytes) =>
                      Some ({| order_id := order_id_value; executed_shares_long := executed_shares_long_value; execution_id := execution_id_value; execution_flags := execution_flags_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessageLongForm.

  Module OrderCancelMessage.

    (** Sent when a visible order on the Cboe book is cancelled in whole or in part. *)
    Record t := {
      order_id : list byte;
      cancelled_shares_short : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (cancelled_shares_short record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 6 (cancelled_shares_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (cancelled_shares_short_value, bytes) =>
              Some ({| order_id := order_id_value; cancelled_shares_short := cancelled_shares_short_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelMessage.

  Module OrderCancelMessageLongForm.

    (** Cboe European platform only. As Order Cancel Message but with a longer Cancelled Shares field. *)
    Record t := {
      order_id : list byte;
      cancelled_shares_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (cancelled_shares_long record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 10 (cancelled_shares_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (cancelled_shares_long_value, bytes) =>
              Some ({| order_id := order_id_value; cancelled_shares_long := cancelled_shares_long_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelMessageLongForm.

  Module TradeMessage.

    (** Provides information about executions of non-displayed orders/shares and negotiated trades. Does not alter the book. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_short : list byte;
      symbol_short : list byte;
      price_short : list byte;
      execution_id : list byte;
      trade_flags : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_short record) = 6 /\
      Datatypes.length (symbol_short record) = 6 /\
      Datatypes.length (price_short record) = 10 /\
      Datatypes.length (execution_id record) = 12 /\
      Datatypes.length (trade_flags record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 6 (shares_short record) ++
      encode_bytes 6 (symbol_short record) ++
      encode_bytes 10 (price_short record) ++
      encode_bytes 12 (execution_id record) ++
      encode_bytes 5 (trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_indicator_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (shares_short_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (symbol_short_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_short_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (execution_id_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (trade_flags_value, bytes) =>
                                  Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; symbol_short := symbol_short_value; price_short := price_short_value; execution_id := execution_id_value; trade_flags := trade_flags_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module TradeMessageLongForm.

    (** Cboe European platform only. As Trade Message but with longer Shares and Price fields. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_long : list byte;
      symbol_long : list byte;
      price_long : list byte;
      execution_id : list byte;
      trade_flags : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_long record) = 10 /\
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (price_long record) = 19 /\
      Datatypes.length (execution_id record) = 12 /\
      Datatypes.length (trade_flags record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 10 (shares_long record) ++
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 19 (price_long record) ++
      encode_bytes 12 (execution_id record) ++
      encode_bytes 5 (trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_indicator_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (shares_long_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (symbol_long_value, bytes) =>
                      match decode_bytes 19 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (execution_id_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (trade_flags_value, bytes) =>
                                  Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_long := shares_long_value; symbol_long := symbol_long_value; price_long := price_long_value; execution_id := execution_id_value; trade_flags := trade_flags_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessageLongForm.

  Module TradeMessageExtendedForm.

    (** Cboe European platform only. Extended details of trades reported to or executed by Cboe (e.g. privately negotiated trades brought on-exchange). *)
    Record t := {
      shares_extended : list byte;
      symbol_long : list byte;
      price_long : list byte;
      trade_id : list byte;
      trade_date : list byte;
      trade_time : list byte;
      execution_venue : list byte;
      currency : list byte;
      cboe_trade_flags : list byte;
      extended_trade_flags : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (shares_extended record) = 12 /\
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (price_long record) = 19 /\
      Datatypes.length (trade_id record) = 12 /\
      Datatypes.length (trade_date record) = 8 /\
      Datatypes.length (trade_time record) = 8 /\
      Datatypes.length (execution_venue record) = 4 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (cboe_trade_flags record) = 1 /\
      Datatypes.length (extended_trade_flags record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (shares_extended record) ++
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 19 (price_long record) ++
      encode_bytes 12 (trade_id record) ++
      encode_bytes 8 (trade_date record) ++
      encode_bytes 8 (trade_time record) ++
      encode_bytes 4 (execution_venue record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (cboe_trade_flags record) ++
      encode_bytes 14 (extended_trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (shares_extended_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 19 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (trade_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (trade_time_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (execution_venue_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (currency_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (cboe_trade_flags_value, bytes) =>
                                          match decode_bytes 14 bytes with
                                          | None => None
                                          | Some (extended_trade_flags_value, bytes) =>
                                              Some ({| shares_extended := shares_extended_value; symbol_long := symbol_long_value; price_long := price_long_value; trade_id := trade_id_value; trade_date := trade_date_value; trade_time := trade_time_value; execution_venue := execution_venue_value; currency := currency_value; cboe_trade_flags := cboe_trade_flags_value; extended_trade_flags := extended_trade_flags_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessageExtendedForm.

  Module TradeMessageUnknownSymbol.

    (** Cboe European Trade Reporting Facility only. Trades reported to Cboe on a symbol not currently known, identified by ISIN and currency. *)
    Record t := {
      shares_extended : list byte;
      symbol_extended : list byte;
      price_long : list byte;
      trade_id : list byte;
      trade_date : list byte;
      trade_time : list byte;
      execution_venue : list byte;
      currency : list byte;
      cboe_trade_flags : list byte;
      extended_trade_flags : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (shares_extended record) = 12 /\
      Datatypes.length (symbol_extended record) = 12 /\
      Datatypes.length (price_long record) = 19 /\
      Datatypes.length (trade_id record) = 12 /\
      Datatypes.length (trade_date record) = 8 /\
      Datatypes.length (trade_time record) = 8 /\
      Datatypes.length (execution_venue record) = 4 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (cboe_trade_flags record) = 1 /\
      Datatypes.length (extended_trade_flags record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (shares_extended record) ++
      encode_bytes 12 (symbol_extended record) ++
      encode_bytes 19 (price_long record) ++
      encode_bytes 12 (trade_id record) ++
      encode_bytes 8 (trade_date record) ++
      encode_bytes 8 (trade_time record) ++
      encode_bytes 4 (execution_venue record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (cboe_trade_flags record) ++
      encode_bytes 14 (extended_trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (shares_extended_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_extended_value, bytes) =>
              match decode_bytes 19 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (trade_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (trade_time_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (execution_venue_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (currency_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (cboe_trade_flags_value, bytes) =>
                                          match decode_bytes 14 bytes with
                                          | None => None
                                          | Some (extended_trade_flags_value, bytes) =>
                                              Some ({| shares_extended := shares_extended_value; symbol_extended := symbol_extended_value; price_long := price_long_value; trade_id := trade_id_value; trade_date := trade_date_value; trade_time := trade_time_value; execution_venue := execution_venue_value; currency := currency_value; cboe_trade_flags := cboe_trade_flags_value; extended_trade_flags := extended_trade_flags_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessageUnknownSymbol.

  Module TradingStatusMessage.

    (** Indicates the current trading status of a security; sent whenever the status changes and for all Suspended securities before trading hours. *)
    Record t := {
      symbol_long : list byte;
      status : list byte;
      reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 3 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (status_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (reserved_value, bytes) =>
                  Some ({| symbol_long := symbol_long_value; status := status_value; reserved := reserved_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module StatisticsMessage.

    (** Cboe European platform only. Disseminates statistics prices: opening, closing, high, low, previous close. *)
    Record t := {
      symbol_long : list byte;
      price_long : list byte;
      statistic_type : list byte;
      price_determination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (price_long record) = 19 /\
      Datatypes.length (statistic_type record) = 1 /\
      Datatypes.length (price_determination record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 19 (price_long record) ++
      encode_bytes 1 (statistic_type record) ++
      encode_bytes 1 (price_determination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          match decode_bytes 19 bytes with
          | None => None
          | Some (price_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (statistic_type_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (price_determination_value, bytes) =>
                      Some ({| symbol_long := symbol_long_value; price_long := price_long_value; statistic_type := statistic_type_value; price_determination := price_determination_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatisticsMessage.

  Module AuctionUpdateMessage.

    (** Disseminates indicative price and size information during auctions for Cboe auction-eligible securities. *)
    Record t := {
      symbol_long : list byte;
      auction_type : list byte;
      reference_price : list byte;
      indicative_price : list byte;
      indicative_shares : list byte;
      outside_tolerance : list byte;
      includes_primary : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (reference_price record) = 19 /\
      Datatypes.length (indicative_price record) = 19 /\
      Datatypes.length (indicative_shares record) = 10 /\
      Datatypes.length (outside_tolerance record) = 1 /\
      Datatypes.length (includes_primary record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 19 (reference_price record) ++
      encode_bytes 19 (indicative_price record) ++
      encode_bytes 10 (indicative_shares record) ++
      encode_bytes 1 (outside_tolerance record) ++
      encode_bytes 1 (includes_primary record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 19 bytes with
              | None => None
              | Some (reference_price_value, bytes) =>
                  match decode_bytes 19 bytes with
                  | None => None
                  | Some (indicative_price_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (indicative_shares_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (outside_tolerance_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (includes_primary_value, bytes) =>
                                  Some ({| symbol_long := symbol_long_value; auction_type := auction_type_value; reference_price := reference_price_value; indicative_price := indicative_price_value; indicative_shares := indicative_shares_value; outside_tolerance := outside_tolerance_value; includes_primary := includes_primary_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionUpdateMessage.

  Module AuctionSummaryMessage.

    (** Disseminates the results of an auction in a Cboe auction-eligible security. *)
    Record t := {
      symbol_long : list byte;
      auction_type : list byte;
      price_long : list byte;
      shares_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (price_long record) = 19 /\
      Datatypes.length (shares_long record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 19 (price_long record) ++
      encode_bytes 10 (shares_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 19 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (shares_long_value, bytes) =>
                      Some ({| symbol_long := symbol_long_value; auction_type := auction_type_value; price_long := price_long_value; shares_long := shares_long_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionSummaryMessage.

  Module LoginRequestPacket.

    (** The Soup 2.0 client must send a Login Request Packet immediately upon establishing a new TCP/IP socket connection to the server. *)
    Record t := {
      username : list byte;
      password : list byte;
      requested_session : list byte;
      requested_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 6 /\
      Datatypes.length (password record) = 10 /\
      Datatypes.length (requested_session record) = 10 /\
      Datatypes.length (requested_sequence_number record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (username record) ++
      encode_bytes 10 (password record) ++
      encode_bytes 10 (requested_session record) ++
      encode_bytes 10 (requested_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (requested_session_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (requested_sequence_number_value, bytes) =>
                      Some ({| username := username_value; password := password_value; requested_session := requested_session_value; requested_sequence_number := requested_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequestPacket.

End BxeEquitiesTcpDepthOfBookV434.
