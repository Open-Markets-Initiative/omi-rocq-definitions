From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Members Exchange Risk Control

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
      - a Reassemble rule
      - the dispatch that chooses a message by its type
      - a block whose stated length holds more than its fields

    License: MIT No Attribution
  *)

Module MemxOptionsRiskControlV16Server.

  Module CommonHeader.

    (** Tcp Common Header *)
    Record t := {
      message_type : N;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_type record < 256 ^ N.of_nat 1)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_type record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_length_value, bytes) =>
              Some ({| message_type := message_type_value; message_length := message_length_value |}, bytes)
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

  End CommonHeader.

  Module LoginAcceptedMessage.

    (** Memx Tcp Login Accepted Message *)
    Record t := {
      supported_request_mode : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (supported_request_mode record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (supported_request_mode record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (supported_request_mode_value, bytes) =>
          Some ({| supported_request_mode := supported_request_mode_value |}, bytes)
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

  End LoginAcceptedMessage.

  Module LoginRejectedMessage.

    (** Memx Tcp Login Rejected Message *)
    Record t := {
      login_reject_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_reject_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_reject_code_value, bytes) =>
          Some ({| login_reject_code := login_reject_code_value |}, bytes)
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

  End LoginRejectedMessage.

  Module StartOfSessionMessage.

    (** Memx Tcp Start of Session Message *)
    Record t := {
      session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          Some ({| session_id := session_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End StartOfSessionMessage.

  Module ReplayBeginMessage.

    (** Memx Tcp Replay Begin Message *)
    Record t := {
      next_sequence_number : N;
      pending_message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (pending_message_count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (next_sequence_number record) ++
      encode_uint 4 (pending_message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (next_sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (pending_message_count_value, bytes) =>
              Some ({| next_sequence_number := next_sequence_number_value; pending_message_count := pending_message_count_value |}, bytes)
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

  End ReplayBeginMessage.

  Module ReplayRejectedMessage.

    (** Memx Tcp Replay Rejected Message *)
    Record t := {
      replay_reject_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (replay_reject_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (replay_reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (replay_reject_code_value, bytes) =>
          Some ({| replay_reject_code := replay_reject_code_value |}, bytes)
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

  End ReplayRejectedMessage.

  Module ReplayCompleteMessage.

    (** Memx Tcp Replay Complete Message *)
    Record t := {
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_count record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (message_count_value, bytes) =>
          Some ({| message_count := message_count_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End ReplayCompleteMessage.

  Module StreamBeginMessage.

    (** Memx Tcp Stream Begin Message *)
    Record t := {
      next_sequence_number : N;
      max_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (max_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (next_sequence_number record) ++
      encode_uint 8 (max_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (next_sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (max_sequence_number_value, bytes) =>
              Some ({| next_sequence_number := next_sequence_number_value; max_sequence_number := max_sequence_number_value |}, bytes)
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

  End StreamBeginMessage.

  Module StreamRejectedMessage.

    (** Memx Tcp Stream Rejected Message *)
    Record t := {
      stream_reject_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stream_reject_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (stream_reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (stream_reject_code_value, bytes) =>
          Some ({| stream_reject_code := stream_reject_code_value |}, bytes)
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

  End StreamRejectedMessage.

  Module StreamCompleteMessage.

    (** Memx Tcp Stream Complete Message *)
    Record t := {
      total_sequence_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (total_sequence_count record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (total_sequence_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (total_sequence_count_value, bytes) =>
          Some ({| total_sequence_count := total_sequence_count_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End StreamCompleteMessage.

  Module SbeHeader.

    (** Sbe Header *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 1)%N /\
      (schema_id record < 256 ^ N.of_nat 1)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (template_id record) ++
      encode_uint 1 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End SbeHeader.

  Module ActiveRiskThresholdStateMessage.

    (** ActiveRiskThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier : list byte;
      efid : list byte;
      threshold_quantity : N;
      unacked_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier record) = 6 /\
      Datatypes.length (efid record) = 4 /\
      (threshold_quantity record < 256 ^ N.of_nat 4)%N /\
      (unacked_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier record) ++
      encode_bytes 4 (efid record) ++
      encode_uint 4 (threshold_quantity record) ++
      encode_uint 4 (unacked_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (threshold_quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (unacked_quantity_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier := underlier_value; efid := efid_value; threshold_quantity := threshold_quantity_value; unacked_quantity := unacked_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveRiskThresholdStateMessage.

  Module ActiveRiskThresholdChangeRejMessage.

    (** ActiveRiskThresholdChangeRejMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      threshold_quantity : N;
      reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (threshold_quantity record < 256 ^ N.of_nat 4)%N /\
      (reject_reason record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 4 (threshold_quantity record) ++
      encode_uint 2 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (threshold_quantity_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (reject_reason_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; threshold_quantity := threshold_quantity_value; reject_reason := reject_reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveRiskThresholdChangeRejMessage.

  Module ActiveRiskAcknowledgedMessage.

    (** ActiveRiskAcknowledgedMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier : list byte;
      efid : list byte;
      quantity : N;
      unacked_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier record) = 6 /\
      Datatypes.length (efid record) = 4 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (unacked_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier record) ++
      encode_bytes 4 (efid record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (unacked_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (unacked_quantity_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier := underlier_value; efid := efid_value; quantity := quantity_value; unacked_quantity := unacked_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveRiskAcknowledgedMessage.

  Module ActiveRiskAcknowledgeRejMessage.

    (** ActiveRiskAcknowledgeRejMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier : list byte;
      efid : list byte;
      threshold_quantity : N;
      reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier record) = 6 /\
      Datatypes.length (efid record) = 4 /\
      (threshold_quantity record < 256 ^ N.of_nat 4)%N /\
      (reject_reason record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier record) ++
      encode_bytes 4 (efid record) ++
      encode_uint 4 (threshold_quantity record) ++
      encode_uint 2 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (threshold_quantity_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (reject_reason_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier := underlier_value; efid := efid_value; threshold_quantity := threshold_quantity_value; reject_reason := reject_reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveRiskAcknowledgeRejMessage.

  Module ActiveRiskQuantityUpdateNotificationMessage.

    (** ActiveRiskQuantityUpdateNotificationMessage *)
    Record t := {
      sending_time : N;
      transact_time : N;
      order_id : N;
      trd_match_id : N;
      efid : list byte;
      underlier : list byte;
      option_security_id : list byte;
      side : list byte;
      last_px : N;
      last_qty : N;
      unacked_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (trd_match_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (efid record) = 4 /\
      Datatypes.length (underlier record) = 6 /\
      Datatypes.length (option_security_id record) = 8 /\
      Datatypes.length (side record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (unacked_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (trd_match_id record) ++
      encode_bytes 4 (efid record) ++
      encode_bytes 6 (underlier record) ++
      encode_bytes 8 (option_security_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 4 (unacked_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sending_time_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (transact_time_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trd_match_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (efid_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (underlier_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (option_security_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_px_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (last_qty_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (unacked_quantity_value, bytes) =>
                                                  Some ({| sending_time := sending_time_value; transact_time := transact_time_value; order_id := order_id_value; trd_match_id := trd_match_id_value; efid := efid_value; underlier := underlier_value; option_security_id := option_security_id_value; side := side_value; last_px := last_px_value; last_qty := last_qty_value; unacked_quantity := unacked_quantity_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ActiveRiskQuantityUpdateNotificationMessage.

  Module CpVolumeThresholdStateMessage.

    (** CPVolumeThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      volume : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (volume record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (volume_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; volume := volume_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpVolumeThresholdStateMessage.

  Module CpExecutedNotionalThresholdStateMessage.

    (** CPExecutedNotionalThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 8)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (price_in_dollars record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpExecutedNotionalThresholdStateMessage.

  Module CpTotalExecutionsThresholdStateMessage.

    (** CPTotalExecutionsThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      total_executions : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (total_executions record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (total_executions record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (total_executions_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; total_executions := total_executions_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpTotalExecutionsThresholdStateMessage.

  Module CpPercentOutstandingContractsThresholdStateMessage.

    (** CPPercentOutstandingContractsThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      percent : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (percent record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 4 (percent record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (percent_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (period_in_milli_seconds_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; percent := percent_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpPercentOutstandingContractsThresholdStateMessage.

  Module CpBreachCountThresholdStateMessage.

    (** CPBreachCountThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      count : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (count record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (count record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (count_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; count := count_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpBreachCountThresholdStateMessage.

  Module ManualCpBreachTriggerPendingMessage.

    (** ManualCPBreachTriggerPendingMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      breach_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (breach_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (breach_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (breach_id_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; breach_id := breach_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ManualCpBreachTriggerPendingMessage.

  Module ManualCpBreachTriggerDoneMessage.

    (** ManualCPBreachTriggerDoneMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      breach_id : N;
      total_affected_orders : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (breach_id record < 256 ^ N.of_nat 8)%N /\
      (total_affected_orders record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (breach_id record) ++
      encode_uint 4 (total_affected_orders record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (breach_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (total_affected_orders_value, bytes) =>
                              Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; breach_id := breach_id_value; total_affected_orders := total_affected_orders_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ManualCpBreachTriggerDoneMessage.

  Module RiskThresholdUpdateRejMessage.

    (** RiskThresholdUpdateRejMessage *)
    Record t := {
      cl_ord_id : list byte;
      risk_type : N;
      reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (risk_type record < 256 ^ N.of_nat 1)%N /\
      (reject_reason record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 1 (risk_type record) ++
      encode_uint 2 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (risk_type_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (reject_reason_value, bytes) =>
                  Some ({| cl_ord_id := cl_ord_id_value; risk_type := risk_type_value; reject_reason := reject_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End RiskThresholdUpdateRejMessage.

  Module PassiveRiskThresholdNotificationMessage.

    (** PassiveRiskThresholdNotificationMessage *)
    Record t := {
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      rule_type : N;
      latest_percentage : N;
      breach_id_optional : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (rule_type record < 256 ^ N.of_nat 1)%N /\
      (latest_percentage record < 256 ^ N.of_nat 1)%N /\
      (breach_id_optional record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 1 (rule_type record) ++
      encode_uint 1 (latest_percentage record) ++
      encode_uint 8 (breach_id_optional record) ++
      encode_uint 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (underlier_optional_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (efid_optional_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (risk_group_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (rule_type_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (latest_percentage_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (breach_id_optional_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; rule_type := rule_type_value; latest_percentage := latest_percentage_value; breach_id_optional := breach_id_optional_value; transact_time := transact_time_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PassiveRiskThresholdNotificationMessage.

  Module SingleOrderAllowIsoOrdersStateMessage.

    (** SingleOrderAllowISOOrdersStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      allow_iso_orders : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (allow_iso_orders record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 1 (allow_iso_orders record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (allow_iso_orders_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; allow_iso_orders := allow_iso_orders_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleOrderAllowIsoOrdersStateMessage.

  Module SingleOrderAllowOrdersInCrossedMarketStateMessage.

    (** SingleOrderAllowOrdersInCrossedMarketStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      allow_orders : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (allow_orders record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 1 (allow_orders record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (allow_orders_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; allow_orders := allow_orders_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleOrderAllowOrdersInCrossedMarketStateMessage.

  Module SingleOrderMaxNotionalThresholdStateMessage.

    (** SingleOrderMaxNotionalThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      max_notional_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (max_notional_in_dollars record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (max_notional_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (max_notional_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; max_notional_in_dollars := max_notional_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleOrderMaxNotionalThresholdStateMessage.

  Module SingleOrderMaxContractsThresholdStateMessage.

    (** SingleOrderMaxContractsThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      max_contracts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (max_contracts record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (max_contracts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (max_contracts_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; max_contracts := max_contracts_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleOrderMaxContractsThresholdStateMessage.

  Module RiskSettingsQueryDoneMessage.

    (** RiskSettingsQueryDoneMessage *)
    Record t := {
      cl_ord_id : list byte;
      number_msgs_sent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (number_msgs_sent record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 4 (number_msgs_sent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (number_msgs_sent_value, bytes) =>
              Some ({| cl_ord_id := cl_ord_id_value; number_msgs_sent := number_msgs_sent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RiskSettingsQueryDoneMessage.

  Module RiskSettingsQueryRejMessage.

    (** RiskSettingsQueryRejMessage *)
    Record t := {
      cl_ord_id : list byte;
      reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (reject_reason record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 2 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (reject_reason_value, bytes) =>
              Some ({| cl_ord_id := cl_ord_id_value; reject_reason := reject_reason_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RiskSettingsQueryRejMessage.

  Module ManualCpBreachTriggerRejMessage.

    (** ManualCPBreachTriggerRejMessage *)
    Record t := {
      cl_ord_id : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (reject_reason record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 2 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (reject_reason_value, bytes) =>
                          Some ({| cl_ord_id := cl_ord_id_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; reject_reason := reject_reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ManualCpBreachTriggerRejMessage.

  Module BreachClearRejMessage.

    (** BreachClearRejMessage *)
    Record t := {
      cl_ord_id : list byte;
      breach_id_optional : N;
      reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id record) = 20 /\
      (breach_id_optional record < 256 ^ N.of_nat 8)%N /\
      (reject_reason record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (breach_id_optional record) ++
      encode_uint 2 (reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (breach_id_optional_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (reject_reason_value, bytes) =>
                  Some ({| cl_ord_id := cl_ord_id_value; breach_id_optional := breach_id_optional_value; reject_reason := reject_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End BreachClearRejMessage.

  Module BreachClearedMessage.

    (** BreachClearedMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      breach_id_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      (breach_id_optional record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_uint 8 (breach_id_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (breach_id_optional_value, bytes) =>
              Some ({| cl_ord_id_optional := cl_ord_id_optional_value; breach_id_optional := breach_id_optional_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BreachClearedMessage.

  Module CpGrossNotionalThresholdStateMessage.

    (** CPGrossNotionalThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (price_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpGrossNotionalThresholdStateMessage.

  Module CpMarketOrderGrossNotionalThresholdStateMessage.

    (** CPMarketOrderGrossNotionalThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (price_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpMarketOrderGrossNotionalThresholdStateMessage.

  Module CpNetNotionalThresholdStateMessage.

    (** CPNetNotionalThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (price_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpNetNotionalThresholdStateMessage.

  Module CpMarketOrderNetNotionalThresholdStateMessage.

    (** CPMarketOrderNetNotionalThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      price_in_dollars : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (price_in_dollars record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 8 (price_in_dollars record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_in_dollars_value, bytes) =>
                          Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; price_in_dollars := price_in_dollars_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpMarketOrderNetNotionalThresholdStateMessage.

  Module CpDuplicateOrderThresholdStateMessage.

    (** CPDuplicateOrderThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      max_dup_orders : N;
      use_order_price_in_dup_check : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (max_dup_orders record < 256 ^ N.of_nat 4)%N /\
      (use_order_price_in_dup_check record < 256 ^ N.of_nat 1)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (max_dup_orders record) ++
      encode_uint 1 (use_order_price_in_dup_check record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (max_dup_orders_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (use_order_price_in_dup_check_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (period_in_milli_seconds_value, bytes) =>
                                  Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; max_dup_orders := max_dup_orders_value; use_order_price_in_dup_check := use_order_price_in_dup_check_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpDuplicateOrderThresholdStateMessage.

  Module CpOrderRateThresholdStateMessage.

    (** CPOrderRateThresholdStateMessage *)
    Record t := {
      cl_ord_id_optional : list byte;
      underlier_optional : list byte;
      efid_optional : list byte;
      risk_group_id : N;
      max_order_msgs : N;
      period_in_milli_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (cl_ord_id_optional record) = 20 /\
      Datatypes.length (underlier_optional record) = 6 /\
      Datatypes.length (efid_optional record) = 4 /\
      (risk_group_id record < 256 ^ N.of_nat 2)%N /\
      (max_order_msgs record < 256 ^ N.of_nat 4)%N /\
      (period_in_milli_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (cl_ord_id_optional record) ++
      encode_bytes 6 (underlier_optional record) ++
      encode_bytes 4 (efid_optional record) ++
      encode_uint 2 (risk_group_id record) ++
      encode_uint 4 (max_order_msgs record) ++
      encode_uint 4 (period_in_milli_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (cl_ord_id_optional_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (underlier_optional_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (efid_optional_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (risk_group_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (max_order_msgs_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (period_in_milli_seconds_value, bytes) =>
                              Some ({| cl_ord_id_optional := cl_ord_id_optional_value; underlier_optional := underlier_optional_value; efid_optional := efid_optional_value; risk_group_id := risk_group_id_value; max_order_msgs := max_order_msgs_value; period_in_milli_seconds := period_in_milli_seconds_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CpOrderRateThresholdStateMessage.

End MemxOptionsRiskControlV16Server.
