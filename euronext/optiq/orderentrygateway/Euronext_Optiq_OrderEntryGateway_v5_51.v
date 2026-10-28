From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Euronext Order Entry Gateway

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
      - a block whose stated length holds more than its fields
      - a Composite rule
      - a run counted by a field
      - a Empty element
  *)

Module EuronextOptiqOrderEntryGatewayV551.

  Module FrameHeader.

    (** Optiq length prefix, read before the message it frames *)
    Record t := {
      frame : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (frame record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (frame record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (frame_value, bytes) =>
          Some ({| frame := frame_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End FrameHeader.

  Module MessageHeader.

    (** Optiq Sbe message header — message identifiers and length of message root *)
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
      encode_uint 2 (block_length record) ++
      encode_uint 2 (template_id record) ++
      encode_uint 2 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 2 bytes with
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

  End MessageHeader.

  Module GroupSizeEncoding.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding.

  Module GroupSizeEncoding2.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding2.

  Module GroupSizeEncoding3.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding3.

  Module GroupSizeEncoding4.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding4.

  Module GroupSizeEncoding5.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding5.

  Module GroupSizeEncoding6.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding6.

  Module GroupSizeEncoding7.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding7.

  Module GroupSizeEncoding8.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding8.

  Module GroupSizeEncoding9.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding9.

  Module GroupSizeEncoding10.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding10.

  Module GroupSizeEncoding11.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding11.

  Module GroupSizeEncoding12.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding12.

  Module GroupSizeEncoding13.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding13.

  Module GroupSizeEncoding14.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding14.

  Module GroupSizeEncoding15.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding15.

  Module GroupSizeEncoding16.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding16.

  Module GroupSizeEncoding17.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding17.

  Module GroupSizeEncoding18.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding18.

  Module GroupSizeEncoding19.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding19.

  Module GroupSizeEncoding20.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding20.

  Module GroupSizeEncoding21.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding21.

  Module GroupSizeEncoding22.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding22.

  Module GroupSizeEncoding23.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding23.

  Module GroupSizeEncoding24.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding24.

  Module GroupSizeEncoding25.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding25.

  Module GroupSizeEncoding26.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding26.

  Module GroupSizeEncoding27.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding27.

  Module GroupSizeEncoding28.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding28.

  Module GroupSizeEncoding29.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding29.

  Module GroupSizeEncoding30.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding30.

  Module GroupSizeEncoding31.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding31.

  Module GroupSizeEncoding32.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding32.

  Module GroupSizeEncoding33.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding33.

  Module GroupSizeEncoding34.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding34.

  Module GroupSizeEncoding35.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding35.

  Module GroupSizeEncoding36.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding36.

  Module GroupSizeEncoding37.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding37.

  Module GroupSizeEncoding38.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding38.

  Module GroupSizeEncoding39.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding39.

  Module GroupSizeEncoding40.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding40.

  Module GroupSizeEncoding41.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding41.

  Module GroupSizeEncoding42.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding42.

  Module GroupSizeEncoding43.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding43.

  Module GroupSizeEncoding44.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding44.

  Module GroupSizeEncoding45.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding45.

  Module GroupSizeEncoding46.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding46.

  Module GroupSizeEncoding47.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding47.

  Module GroupSizeEncoding48.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding48.

  Module GroupSizeEncoding49.

    (** groupSizeEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding49.

End EuronextOptiqOrderEntryGatewayV551.
