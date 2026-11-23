From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Moscow Exchange TWIME Spectra Order Entry

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
      - a field read in bits
      - a block whose stated length holds more than its fields

    License: MIT No Attribution
  *)

Module SpectraOrderEntryV9120Server.

  Module SbeHeader.

    (** Message body length, message id, message scheme id and message scheme version *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (schema_id record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (block_length record) ++
      encode_uint_le 2 (template_id record) ++
      encode_uint_le 2 (schema_id record) ++
      encode_uint_le 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint_le 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SbeHeader.

  Module EstablishmentAckMessage.

    (** EstablishmentAckMessage *)
    Record t := {
      request_timestamp : N;
      keepalive_interval : N;
      next_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (keepalive_interval record < 256 ^ N.of_nat 4)%N /\
      (next_seq_no record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (request_timestamp record) ++
      encode_uint_le 4 (keepalive_interval record) ++
      encode_uint_le 8 (next_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (request_timestamp_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (keepalive_interval_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (next_seq_no_value, bytes) =>
                  Some ({| request_timestamp := request_timestamp_value; keepalive_interval := keepalive_interval_value; next_seq_no := next_seq_no_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EstablishmentAckMessage.

  Module EstablishmentRejectMessage.

    (** EstablishmentRejectMessage *)
    Record t := {
      request_timestamp : N;
      establishment_reject_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (establishment_reject_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (request_timestamp record) ++
      encode_uint 1 (establishment_reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (request_timestamp_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (establishment_reject_code_value, bytes) =>
              Some ({| request_timestamp := request_timestamp_value; establishment_reject_code := establishment_reject_code_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EstablishmentRejectMessage.

  Module TerminateMessage.

    (** TerminateMessage *)
    Record t := {
      termination_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (termination_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (termination_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (termination_code_value, bytes) =>
          Some ({| termination_code := termination_code_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End TerminateMessage.

  Module RetransmissionMessage.

    (** RetransmissionMessage *)
    Record t := {
      next_seq_no : N;
      request_timestamp : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_seq_no record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (next_seq_no record) ++
      encode_uint_le 8 (request_timestamp record) ++
      encode_uint_le 4 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (next_seq_no_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (request_timestamp_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (count_value, bytes) =>
                  Some ({| next_seq_no := next_seq_no_value; request_timestamp := request_timestamp_value; count := count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RetransmissionMessage.

  Module SequenceMessage.

    (** SequenceMessage *)
    Record t := {
      next_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_seq_no record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (next_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (next_seq_no_value, bytes) =>
          Some ({| next_seq_no := next_seq_no_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint_le by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SequenceMessage.

  Module FloodRejectMessage.

    (** FloodRejectMessage *)
    Record t := {
      cl_ord_id : N;
      queue_size : N;
      penalty_remain : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (queue_size record < 256 ^ N.of_nat 4)%N /\
      (penalty_remain record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (cl_ord_id record) ++
      encode_uint_le 4 (queue_size record) ++
      encode_uint_le 4 (penalty_remain record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (queue_size_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (penalty_remain_value, bytes) =>
                  Some ({| cl_ord_id := cl_ord_id_value; queue_size := queue_size_value; penalty_remain := penalty_remain_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End FloodRejectMessage.

  Module SessionRejectMessage.

    (** SessionRejectMessage *)
    Record t := {
      cl_ord_id : N;
      ref_tag_id : N;
      session_reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (ref_tag_id record < 256 ^ N.of_nat 4)%N /\
      (session_reject_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (cl_ord_id record) ++
      encode_uint_le 4 (ref_tag_id record) ++
      encode_uint 1 (session_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (ref_tag_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_reject_reason_value, bytes) =>
                  Some ({| cl_ord_id := cl_ord_id_value; ref_tag_id := ref_tag_id_value; session_reject_reason := session_reject_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SessionRejectMessage.

  Module BusinessMessageRejectMessage.

    (** BusinessMessageRejectMessage *)
    Record t := {
      cl_ord_id : N;
      timestamp : N;
      ord_rej_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (ord_rej_reason record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (cl_ord_id record) ++
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 4 (ord_rej_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (ord_rej_reason_value, bytes) =>
                  Some ({| cl_ord_id := cl_ord_id_value; timestamp := timestamp_value; ord_rej_reason := ord_rej_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BusinessMessageRejectMessage.

  Module OrderMassCancelResponseMessage.

    (** OrderMassCancelResponseMessage *)
    Record t := {
      cl_ord_id : N;
      timestamp : N;
      total_affected_orders : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (total_affected_orders record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (cl_ord_id record) ++
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 4 (total_affected_orders record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (cl_ord_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (total_affected_orders_value, bytes) =>
                  Some ({| cl_ord_id := cl_ord_id_value; timestamp := timestamp_value; total_affected_orders := total_affected_orders_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderMassCancelResponseMessage.

  Module EmptyBookMessage.

    (** EmptyBookMessage *)
    Record t := {
      timestamp : N;
      trading_session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (trading_session_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 4 (trading_session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (trading_session_id_value, bytes) =>
              Some ({| timestamp := timestamp_value; trading_session_id := trading_session_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EmptyBookMessage.

  Module SystemEventMessage.

    (** SystemEventMessage *)
    Record t := {
      timestamp : N;
      event_id : N;
      trading_session_id : N;
      trad_ses_event : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (event_id record < 256 ^ N.of_nat 8)%N /\
      (trading_session_id record < 256 ^ N.of_nat 4)%N /\
      (trad_ses_event record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (event_id record) ++
      encode_uint_le 4 (trading_session_id record) ++
      encode_uint 1 (trad_ses_event record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (event_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (trading_session_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trad_ses_event_value, bytes) =>
                      Some ({| timestamp := timestamp_value; event_id := event_id_value; trading_session_id := trading_session_id_value; trad_ses_event := trad_ses_event_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SystemEventMessage.

End SpectraOrderEntryV9120Server.
