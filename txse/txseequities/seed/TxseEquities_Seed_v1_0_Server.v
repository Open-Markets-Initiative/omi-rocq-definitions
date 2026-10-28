From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Texas Stock Exchange Session Enabled Entry Daemon

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
      - a length prefix framing what follows
      - a field read in bits
      - a field present only on a condition
  *)

Module TxseEquitiesSeedV10Server.

  Module RakeMessageHeader.

    (** Rake Tcp per-message header carrying the frame length and packet-level dispatch byte *)
    Record t := {
      message_length : N;
      packet_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (packet_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (packet_type_value, bytes) =>
              Some ({| message_length := message_length_value; packet_type := packet_type_value |}, bytes)
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

  End RakeMessageHeader.

  Module LogonResponseMessage.

    (** Response to a logon request *)
    Record t := {
      session : N;
      next_sequence_number : N;
      highest_known_sequence_number : N;
      logon_response_code : N;
      number_stream_ids : N;
      instance : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session record < 256 ^ N.of_nat 8)%N /\
      (next_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (highest_known_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (logon_response_code record < 256 ^ N.of_nat 1)%N /\
      (number_stream_ids record < 256 ^ N.of_nat 1)%N /\
      (instance record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (session record) ++
      encode_uint 8 (next_sequence_number record) ++
      encode_uint 8 (highest_known_sequence_number record) ++
      encode_uint 1 (logon_response_code record) ++
      encode_uint 1 (number_stream_ids record) ++
      encode_uint 4 (instance record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (next_sequence_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (highest_known_sequence_number_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (logon_response_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (number_stream_ids_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (instance_value, bytes) =>
                              Some ({| session := session_value; next_sequence_number := next_sequence_number_value; highest_known_sequence_number := highest_known_sequence_number_value; logon_response_code := logon_response_code_value; number_stream_ids := number_stream_ids_value; instance := instance_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End LogonResponseMessage.

  Module OrderCanceledMessage.

    (** This order has been canceled. No shares are left on the Exchange. The Member will receive this message in response to a CancelOrder message, as well as unsolicited messages from the Exchange for various reasons. *)
    Record t := {
      transact_time : N;
      order_id : N;
      orig_cl_ord_id : N;
      cancel_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (orig_cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (cancel_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (orig_cl_ord_id record) ++
      encode_uint 1 (cancel_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (orig_cl_ord_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (cancel_reason_value, bytes) =>
                      Some ({| transact_time := transact_time_value; order_id := order_id_value; orig_cl_ord_id := orig_cl_ord_id_value; cancel_reason := cancel_reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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

  End OrderCanceledMessage.

  Module CancelRejectedMessage.

    (** The requested CancelOrder has been rejected. *)
    Record t := {
      transact_time : N;
      orig_cl_ord_id : N;
      cancel_rejected_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (orig_cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (cancel_rejected_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (orig_cl_ord_id record) ++
      encode_uint 1 (cancel_rejected_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (orig_cl_ord_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (cancel_rejected_reason_value, bytes) =>
                  Some ({| transact_time := transact_time_value; orig_cl_ord_id := orig_cl_ord_id_value; cancel_rejected_reason := cancel_rejected_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End CancelRejectedMessage.

  Module MassCancelResultMessage.

    (** Confirms sweep completion. Sent after all affected orders have been canceled. *)
    Record t := {
      transact_time : N;
      mass_cancel_request_id : N;
      mass_cancel_id : N;
      canceled_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (mass_cancel_request_id record < 256 ^ N.of_nat 8)%N /\
      (mass_cancel_id record < 256 ^ N.of_nat 8)%N /\
      (canceled_count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (mass_cancel_request_id record) ++
      encode_uint 8 (mass_cancel_id record) ++
      encode_uint 4 (canceled_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (mass_cancel_request_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (mass_cancel_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (canceled_count_value, bytes) =>
                      Some ({| transact_time := transact_time_value; mass_cancel_request_id := mass_cancel_request_id_value; mass_cancel_id := mass_cancel_id_value; canceled_count := canceled_count_value |}, bytes)
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

  End MassCancelResultMessage.

End TxseEquitiesSeedV10Server.
