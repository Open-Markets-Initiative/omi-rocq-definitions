From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * CIX Trading Inc. CIX Udp Rerequest

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

Module CixAtsCixAspenRerequestV11.

  Module RerequestHeader.

    (** Aspen Udp rerequest header *)
    Record t := {
      market_day_identifier : list byte;
      feed_identifier : list byte;
      sequence : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_day_identifier record) = 9 /\
      Datatypes.length (feed_identifier record) = 1 /\
      (sequence record < 256 ^ N.of_nat 8)%N /\
      (count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (market_day_identifier record) ++
      encode_bytes 1 (feed_identifier record) ++
      encode_uint 8 (sequence record) ++
      encode_uint 2 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (market_day_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (feed_identifier_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sequence_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (count_value, bytes) =>
                      Some ({| market_day_identifier := market_day_identifier_value; feed_identifier := feed_identifier_value; sequence := sequence_value; count := count_value |}, bytes)
                  end
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

  End RerequestHeader.

  Module Packet.

    (** Aspen Udp Rerequest Packet *)
    Record t := {
      rerequest_header : RerequestHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      RerequestHeader.bounded (rerequest_header record).

    Definition encode (record : t) : list byte :=
      RerequestHeader.encode (rerequest_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match RerequestHeader.decode bytes with
      | None => None
      | Some (rerequest_header_value, bytes) =>
          Some ({| rerequest_header := rerequest_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !RerequestHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite RerequestHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply RerequestHeader.eq_dec]. Defined.

  End Packet.

End CixAtsCixAspenRerequestV11.
