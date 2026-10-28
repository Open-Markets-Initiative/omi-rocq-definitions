From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd Mtbt Order Book Snapshot Recovery

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
      - a run counted by a field
      - a Composite rule
  *)

Module NseComSnapshotV71Tcp.

  Module SnapshotHeader.

    (** Snapshot header has a size of 16 bytes *)
    Record t := {
      trans_code : N;
      size : N;
      number_of_records : N;
      last_sequence_number : N;
      stream_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trans_code record < 256 ^ N.of_nat 2)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (number_of_records record < 256 ^ N.of_nat 4)%N /\
      (last_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (stream_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (trans_code record) ++
      encode_uint 4 (size record) ++
      encode_uint 4 (number_of_records record) ++
      encode_uint 4 (last_sequence_number record) ++
      encode_uint 2 (stream_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (trans_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (size_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (number_of_records_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (last_sequence_number_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (stream_id_value, bytes) =>
                          Some ({| trans_code := trans_code_value; size := size_value; number_of_records := number_of_records_value; last_sequence_number := last_sequence_number_value; stream_id := stream_id_value |}, bytes)
                      end
                  end
              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SnapshotHeader.

End NseComSnapshotV71Tcp.
