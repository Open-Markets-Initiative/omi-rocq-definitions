From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Members Exchange Common Header

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
      - a run counted by a field
  *)

Module MemxEquitiesCommonHeaderV11.

  Module CommonHeader.

    (** Common Header *)
    Record t := {
      message_type : N;
      header_length : N;
      session_id : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_type record < 256 ^ N.of_nat 1)%N /\
      (header_length record < 256 ^ N.of_nat 1)%N /\
      (session_id record < 256 ^ N.of_nat 8)%N /\
      (sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_type record) ++
      encode_uint 1 (header_length record) ++
      encode_uint 8 (session_id record) ++
      encode_uint 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (header_length_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      Some ({| message_type := message_type_value; header_length := header_length_value; session_id := session_id_value; sequence_number := sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End CommonHeader.

End MemxEquitiesCommonHeaderV11.
