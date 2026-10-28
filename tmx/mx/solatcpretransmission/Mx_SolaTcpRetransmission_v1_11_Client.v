From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * TMX Group Sola Tcp Retransmission

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
  *)

Module MxSolaTcpRetransmissionV111Client.

  Module ClientMessageHeader.

    (** Standard Hsvf message header *)
    Record t := {
      sequence_number : list byte;
      client_message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sequence_number record) = 9 /\
      Datatypes.length (client_message_type record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (sequence_number record) ++
      encode_bytes 2 (client_message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (client_message_type_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; client_message_type := client_message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClientMessageHeader.

  Module LoginMessage.

    (** Login *)
    Record t := {
      user : list byte;
      pwd : list byte;
      login_timestamp : list byte;
      protocol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user record) = 16 /\
      Datatypes.length (pwd record) = 16 /\
      Datatypes.length (login_timestamp record) = 6 /\
      Datatypes.length (protocol record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (user record) ++
      encode_bytes 16 (pwd record) ++
      encode_bytes 6 (login_timestamp record) ++
      encode_bytes 2 (protocol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (user_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (pwd_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (login_timestamp_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (protocol_value, bytes) =>
                      Some ({| user := user_value; pwd := pwd_value; login_timestamp := login_timestamp_value; protocol := protocol_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End LoginMessage.

  Module RetransmissionRequestMessage.

    (** Retransmission Request *)
    Record t := {
      line : list byte;
      start : list byte;
      end_ : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (line record) = 2 /\
      Datatypes.length (start record) = 9 /\
      Datatypes.length (end_ record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (line record) ++
      encode_bytes 9 (start record) ++
      encode_bytes 9 (end_ record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (line_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (start_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (end__value, bytes) =>
                  Some ({| line := line_value; start := start_value; end_ := end__value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmissionRequestMessage.

End MxSolaTcpRetransmissionV111Client.
