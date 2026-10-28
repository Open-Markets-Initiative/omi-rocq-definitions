From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * TMX Group Quantum Feed Level 2 Recovery

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
      - a run counted by a field
  *)

Module TsxAlphaQuantumFeedLevel2RecoveryV21Client.

  Module FrameHeader.

    (** XMT frame prefix and outer header. *)
    Record t := {
      start_of_frame : N;
      protocol_name : list byte;
      protocol_version : list byte;
      message_length : N;
      session_id : N;
      ack_required_poss_dup : list byte;
      num_body : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_of_frame record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (protocol_name record) = 1 /\
      Datatypes.length (protocol_version record) = 1 /\
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ack_required_poss_dup record) = 1 /\
      (num_body record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (start_of_frame record) ++
      encode_bytes 1 (protocol_name record) ++
      encode_bytes 1 (protocol_version record) ++
      encode_uint 2 (message_length record) ++
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (ack_required_poss_dup record) ++
      encode_uint 1 (num_body record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (start_of_frame_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (protocol_name_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (protocol_version_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (message_length_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (session_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (ack_required_poss_dup_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (num_body_value, bytes) =>
                                  Some ({| start_of_frame := start_of_frame_value; protocol_name := protocol_name_value; protocol_version := protocol_version_value; message_length := message_length_value; session_id := session_id_value; ack_required_poss_dup := ack_required_poss_dup_value; num_body := num_body_value |}, bytes)
                              end
                          end
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FrameHeader.

  Module BodyHeader.

    (** Xmt Body Header *)
    Record t := {
      msg_length : N;
      msg_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (msg_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_length record) ++
      encode_bytes 1 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_length := msg_length_value; msg_type := msg_type_value |}, bytes)
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

  End BodyHeader.

  Module BodyHeader2.

    (** Xmt Body Header *)
    Record t := {
      msg_length : N;
      msg_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (msg_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_length record) ++
      encode_bytes 1 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_length := msg_length_value; msg_type := msg_type_value |}, bytes)
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

  End BodyHeader2.

  Module BodyHeader3.

    (** Xmt Body Header *)
    Record t := {
      msg_length : N;
      msg_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (msg_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_length record) ++
      encode_bytes 1 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_length := msg_length_value; msg_type := msg_type_value |}, bytes)
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

  End BodyHeader3.

  Module BodyHeader4.

    (** Xmt Body Header *)
    Record t := {
      msg_length : N;
      msg_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (msg_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_length record) ++
      encode_bytes 1 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_length := msg_length_value; msg_type := msg_type_value |}, bytes)
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

  End BodyHeader4.

End TsxAlphaQuantumFeedLevel2RecoveryV21Client.
