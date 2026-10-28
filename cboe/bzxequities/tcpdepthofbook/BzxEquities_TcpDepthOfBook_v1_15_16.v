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

Module BzxEquitiesTcpDepthOfBookV11516.

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

    (** Sequenced Message Header *)
    Record t := {
      timestamp : list byte;
      sequenced_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (timestamp record) = 8 /\
      Datatypes.length (sequenced_message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (timestamp record) ++
      encode_bytes 1 (sequenced_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sequenced_message_type_value, bytes) =>
              Some ({| timestamp := timestamp_value; sequenced_message_type := sequenced_message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

    (** The Symbol Clear message instructs feed recipients to clear all orders for the Cboe book in the specified symbol. *)
    Record t := {
      stock_symbol_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol_long record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_long_value, bytes) =>
          Some ({| stock_symbol_long := stock_symbol_long_value |}, bytes)
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

  Module AddOrderShortMessage.

    (** An Add Order message represents a newly accepted visible order on the Cboe book. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_short : list byte;
      stock_symbol_short : list byte;
      price_short : list byte;
      reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_short record) = 6 /\
      Datatypes.length (stock_symbol_short record) = 6 /\
      Datatypes.length (price_short record) = 10 /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 6 (shares_short record) ++
      encode_bytes 6 (stock_symbol_short record) ++
      encode_bytes 10 (price_short record) ++
      encode_bytes 1 (reserved record).

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
                  | Some (stock_symbol_short_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; stock_symbol_short := stock_symbol_short_value; price_short := price_short_value; reserved := reserved_value |}, bytes)
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

  End AddOrderShortMessage.

  Module AddOrderLongMessage.

    (** The long version of the Add Order message accommodates larger symbol sizes possible through the ISRA plan. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_short : list byte;
      stock_symbol_long : list byte;
      price_short : list byte;
      reserved : list byte;
      participant_id : list byte;
      customer_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_short record) = 6 /\
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (price_short record) = 10 /\
      Datatypes.length (reserved record) = 1 /\
      Datatypes.length (participant_id record) = 4 /\
      Datatypes.length (customer_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 6 (shares_short record) ++
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 10 (price_short record) ++
      encode_bytes 1 (reserved record) ++
      encode_bytes 4 (participant_id record) ++
      encode_bytes 1 (customer_indicator record).

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
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (stock_symbol_long_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_short_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (participant_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (customer_indicator_value, bytes) =>
                                      Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; stock_symbol_long := stock_symbol_long_value; price_short := price_short_value; reserved := reserved_value; participant_id := participant_id_value; customer_indicator := customer_indicator_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderLongMessage.

  Module AddOrderExtendedMessage.

    (** The extended version of the Add Order message accommodates larger prices. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_short : list byte;
      stock_symbol_long : list byte;
      price_long : list byte;
      display : list byte;
      participant_id : list byte;
      customer_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_short record) = 6 /\
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (price_long record) = 14 /\
      Datatypes.length (display record) = 1 /\
      Datatypes.length (participant_id record) = 4 /\
      Datatypes.length (customer_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 6 (shares_short record) ++
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 14 (price_long record) ++
      encode_bytes 1 (display record) ++
      encode_bytes 4 (participant_id record) ++
      encode_bytes 1 (customer_indicator record).

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
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (stock_symbol_long_value, bytes) =>
                      match decode_bytes 14 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (display_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (participant_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (customer_indicator_value, bytes) =>
                                      Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; stock_symbol_long := stock_symbol_long_value; price_long := price_long_value; display := display_value; participant_id := participant_id_value; customer_indicator := customer_indicator_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderExtendedMessage.

  Module OrderExecutedMessage.

    (** Order Executed messages are sent when a visible order on the Cboe book is executed in whole or in part. *)
    Record t := {
      order_id : list byte;
      executed_shares : list byte;
      execution_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (executed_shares record) = 6 /\
      Datatypes.length (execution_id record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 6 (executed_shares record) ++
      encode_bytes 12 (execution_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (executed_shares_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (execution_id_value, bytes) =>
                  Some ({| order_id := order_id_value; executed_shares := executed_shares_value; execution_id := execution_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End OrderExecutedMessage.

  Module OrderCancelMessage.

    (** Order Cancel messages are sent when a visible order on the Cboe book is canceled in whole or in part. *)
    Record t := {
      order_id : list byte;
      canceled_shares : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (canceled_shares record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 6 (canceled_shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (canceled_shares_value, bytes) =>
              Some ({| order_id := order_id_value; canceled_shares := canceled_shares_value |}, bytes)
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

  Module TimeReferenceMessage.

    (** The Time Reference message is used to provide a midnight reference point for recipients of the feed. It is sent whenever the system starts up and when the system crosses a midnight boundary. All subsequent Timestamp values will use the last Midnight Reference until another Time Reference message is received. The Timestamp field will contain the offset from the Trade Date of the Time Reference message. *)
    Record t := {
      midnight_reference : list byte;
      time : list byte;
      trade_date : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (midnight_reference record) = 10 /\
      Datatypes.length (time record) = 10 /\
      Datatypes.length (trade_date record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (midnight_reference record) ++
      encode_bytes 10 (time record) ++
      encode_bytes 8 (trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (midnight_reference_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (time_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trade_date_value, bytes) =>
                  Some ({| midnight_reference := midnight_reference_value; time := time_value; trade_date := trade_date_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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

  End TimeReferenceMessage.

  Module TradeShortMessage.

    (** The Trade message provides information about executions of non-displayed orders or shares on the Cboe book and routed orders. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_short : list byte;
      stock_symbol_short : list byte;
      price_short : list byte;
      execution_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_short record) = 6 /\
      Datatypes.length (stock_symbol_short record) = 6 /\
      Datatypes.length (price_short record) = 10 /\
      Datatypes.length (execution_id record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 6 (shares_short record) ++
      encode_bytes 6 (stock_symbol_short record) ++
      encode_bytes 10 (price_short record) ++
      encode_bytes 12 (execution_id record).

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
                  | Some (stock_symbol_short_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_short_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (execution_id_value, bytes) =>
                              Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; stock_symbol_short := stock_symbol_short_value; price_short := price_short_value; execution_id := execution_id_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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

  End TradeShortMessage.

  Module TradeLongMessage.

    (** The long version of the Trade message accommodates larger symbol sizes possible through the ISRA plan. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_short : list byte;
      stock_symbol_long : list byte;
      price_short : list byte;
      execution_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_short record) = 6 /\
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (price_short record) = 10 /\
      Datatypes.length (execution_id record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 6 (shares_short record) ++
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 10 (price_short record) ++
      encode_bytes 12 (execution_id record).

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
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (stock_symbol_long_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (price_short_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (execution_id_value, bytes) =>
                              Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; stock_symbol_long := stock_symbol_long_value; price_short := price_short_value; execution_id := execution_id_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
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

  End TradeLongMessage.

  Module TradeExtendedMessage.

    (** The extended version of the Trade message accommodates larger prices. *)
    Record t := {
      order_id : list byte;
      side_indicator : list byte;
      shares_short : list byte;
      stock_symbol_long : list byte;
      price_long : list byte;
      execution_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_id record) = 12 /\
      Datatypes.length (side_indicator record) = 1 /\
      Datatypes.length (shares_short record) = 6 /\
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (price_long record) = 14 /\
      Datatypes.length (execution_id record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_bytes 6 (shares_short record) ++
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 14 (price_long record) ++
      encode_bytes 12 (execution_id record).

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
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (stock_symbol_long_value, bytes) =>
                      match decode_bytes 14 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (execution_id_value, bytes) =>
                              Some ({| order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; stock_symbol_long := stock_symbol_long_value; price_long := price_long_value; execution_id := execution_id_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
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

  End TradeExtendedMessage.

  Module TradeBreakMessage.

    (** The Trade Break message is sent whenever an execution on Cboe is broken. *)
    Record t := {
      execution_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (execution_id record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (execution_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (execution_id_value, bytes) =>
          Some ({| execution_id := execution_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End TradeBreakMessage.

  Module TradingStatusMessage.

    (** The Trading Status message is used to indicate the current trading status of a security. *)
    Record t := {
      stock_symbol_long : list byte;
      halt_status : list byte;
      reg_sho_action : list byte;
      reserved_1 : list byte;
      reserved_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (halt_status record) = 1 /\
      Datatypes.length (reg_sho_action record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (reserved_2 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 1 (halt_status record) ++
      encode_bytes 1 (reg_sho_action record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (halt_status_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reg_sho_action_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reserved_2_value, bytes) =>
                          Some ({| stock_symbol_long := stock_symbol_long_value; halt_status := halt_status_value; reg_sho_action := reg_sho_action_value; reserved_1 := reserved_1_value; reserved_2 := reserved_2_value |}, bytes)
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module AuctionUpdateMessage.

    (** Auction Update messages are used to disseminate Cboe price and size information during auctions for Cboe listed securities on BZX, and for Periodic Auctions on BYX. *)
    Record t := {
      stock_symbol_long : list byte;
      auction_type : list byte;
      reference_price_short : list byte;
      buy_shares : list byte;
      sell_shares : list byte;
      indicative_price_short : list byte;
      auction_only_price_short : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (reference_price_short record) = 10 /\
      Datatypes.length (buy_shares record) = 10 /\
      Datatypes.length (sell_shares record) = 10 /\
      Datatypes.length (indicative_price_short record) = 10 /\
      Datatypes.length (auction_only_price_short record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 10 (reference_price_short record) ++
      encode_bytes 10 (buy_shares record) ++
      encode_bytes 10 (sell_shares record) ++
      encode_bytes 10 (indicative_price_short record) ++
      encode_bytes 10 (auction_only_price_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (reference_price_short_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (buy_shares_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (sell_shares_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (indicative_price_short_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (auction_only_price_short_value, bytes) =>
                                  Some ({| stock_symbol_long := stock_symbol_long_value; auction_type := auction_type_value; reference_price_short := reference_price_short_value; buy_shares := buy_shares_value; sell_shares := sell_shares_value; indicative_price_short := indicative_price_short_value; auction_only_price_short := auction_only_price_short_value |}, bytes)
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

  Module ExtendedAuctionUpdateMessage.

    (** The extended version of the BZX Auction Update message accommodates larger prices. *)
    Record t := {
      stock_symbol_long : list byte;
      auction_type : list byte;
      reference_price_long : list byte;
      buy_shares : list byte;
      sell_shares : list byte;
      indicative_price_long : list byte;
      auction_only_price_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (reference_price_long record) = 14 /\
      Datatypes.length (buy_shares record) = 10 /\
      Datatypes.length (sell_shares record) = 10 /\
      Datatypes.length (indicative_price_long record) = 14 /\
      Datatypes.length (auction_only_price_long record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 14 (reference_price_long record) ++
      encode_bytes 10 (buy_shares record) ++
      encode_bytes 10 (sell_shares record) ++
      encode_bytes 14 (indicative_price_long record) ++
      encode_bytes 14 (auction_only_price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (reference_price_long_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (buy_shares_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (sell_shares_value, bytes) =>
                          match decode_bytes 14 bytes with
                          | None => None
                          | Some (indicative_price_long_value, bytes) =>
                              match decode_bytes 14 bytes with
                              | None => None
                              | Some (auction_only_price_long_value, bytes) =>
                                  Some ({| stock_symbol_long := stock_symbol_long_value; auction_type := auction_type_value; reference_price_long := reference_price_long_value; buy_shares := buy_shares_value; sell_shares := sell_shares_value; indicative_price_long := indicative_price_long_value; auction_only_price_long := auction_only_price_long_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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

  End ExtendedAuctionUpdateMessage.

  Module AuctionSummaryMessage.

    (** Auction Summary messages are used to disseminate the results of an auction of a Cboe listed security on BZX, and for Periodic Auctions on BYX. *)
    Record t := {
      stock_symbol_long : list byte;
      auction_type : list byte;
      price_short : list byte;
      shares_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (price_short record) = 10 /\
      Datatypes.length (shares_long record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 10 (price_short record) ++
      encode_bytes 10 (shares_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (price_short_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (shares_long_value, bytes) =>
                      Some ({| stock_symbol_long := stock_symbol_long_value; auction_type := auction_type_value; price_short := price_short_value; shares_long := shares_long_value |}, bytes)
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

  End AuctionSummaryMessage.

  Module ExtendedAuctionSummaryMessage.

    (** The extended version of the Auction Summary message accommodates larger prices. *)
    Record t := {
      stock_symbol_long : list byte;
      auction_type : list byte;
      price_long : list byte;
      shares_long : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (price_long record) = 14 /\
      Datatypes.length (shares_long record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 14 (price_long record) ++
      encode_bytes 10 (shares_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (auction_type_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (shares_long_value, bytes) =>
                      Some ({| stock_symbol_long := stock_symbol_long_value; auction_type := auction_type_value; price_long := price_long_value; shares_long := shares_long_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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

  End ExtendedAuctionSummaryMessage.

  Module RetailPriceImprovementMessage.

    (** The Retail Price Improvement message is only available on the BYX and EDGX Exchanges. This message is a Retail Liquidity Indicator (RLI) that includes symbol and side, but not price and size. *)
    Record t := {
      stock_symbol_long : list byte;
      retail_price_improvement : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_symbol_long record) = 8 /\
      Datatypes.length (retail_price_improvement record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock_symbol_long record) ++
      encode_bytes 1 (retail_price_improvement record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_symbol_long_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (retail_price_improvement_value, bytes) =>
              Some ({| stock_symbol_long := stock_symbol_long_value; retail_price_improvement := retail_price_improvement_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End RetailPriceImprovementMessage.

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

End BzxEquitiesTcpDepthOfBookV11516.
