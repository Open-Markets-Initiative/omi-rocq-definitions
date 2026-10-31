From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Tradelogiq Markets Inc. Lynx Multicast Level 1

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
  *)

Module LynxAtsMulticastLevel1V101Request.

  Module RequestPacket.

    (** Sent to a Re-request server to request the retransmission of a particular message or group of messages *)
    Record t := {
      request_session : list byte;
      request_sequence_number : N;
      requested_message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (request_session record) = 10 /\
      (request_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (requested_message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (request_session record) ++
      encode_uint 8 (request_sequence_number record) ++
      encode_uint 2 (requested_message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (request_session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (request_sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (requested_message_count_value, bytes) =>
                  Some ({| request_session := request_session_value; request_sequence_number := request_sequence_number_value; requested_message_count := requested_message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End RequestPacket.

End LynxAtsMulticastLevel1V101Request.
