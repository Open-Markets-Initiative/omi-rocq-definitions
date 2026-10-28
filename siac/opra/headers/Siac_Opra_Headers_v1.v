From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Securities Industry Automation Corporation Headers

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
      - a length prefix framing what follows
  *)

Module SiacOpraHeadersV1.

  Module ControlMessage.

    (** Control message *)
    Record t := {
      control_message_type : list byte;
      message_indicator : list byte;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (control_message_type record) = 1 /\
      Datatypes.length (message_indicator record) = 1 /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (control_message_type record) ++
      encode_bytes 1 (message_indicator record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 4 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (control_message_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_indicator_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (transaction_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (participant_reference_number_value, bytes) =>
                      Some ({| control_message_type := control_message_type_value; message_indicator := message_indicator_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ControlMessage.

End SiacOpraHeadersV1.
