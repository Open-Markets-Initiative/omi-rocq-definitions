From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Securities Industry Automation Corporation 

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
      - a Composite rule
      - a run counted by a field
      - the dispatch that chooses a message by its type
  *)

Module SiacCtsOutputV211B.

  Module SaleCondition4.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition4.

  Module SaleCondition42.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition42.

  Module SaleCondition43.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition43.

  Module SaleCondition44.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition44.

  Module SaleCondition45.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition45.

  Module SaleCondition46.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition46.

  Module SaleCondition47.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition47.

  Module SaleCondition48.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition48.

  Module SaleCondition49.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SaleCondition49.

End SiacCtsOutputV211B.
