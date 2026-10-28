From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Investors Exchange IexTp Header

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

Module IexEquitiesIexTpHeaderV10.

  Module IextpHeader.

    (** IexTp packet header *)
    Record t := {
      version : N;
      reserved : N;
      message_protocol_id : N;
      channel_id : N;
      session_id : N;
      payload_length : N;
      message_count : N;
      stream_offset : N;
      first_message_sequence_number : N;
      send_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 1)%N /\
      (reserved record < 256 ^ N.of_nat 1)%N /\
      (message_protocol_id record < 256 ^ N.of_nat 2)%N /\
      (channel_id record < 256 ^ N.of_nat 4)%N /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (payload_length record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N /\
      (stream_offset record < 256 ^ N.of_nat 8)%N /\
      (first_message_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (send_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record) ++
      encode_uint 1 (reserved record) ++
      encode_uint 2 (message_protocol_id record) ++
      encode_uint 4 (channel_id record) ++
      encode_uint 4 (session_id record) ++
      encode_uint 2 (payload_length record) ++
      encode_uint 2 (message_count record) ++
      encode_uint 8 (stream_offset record) ++
      encode_uint 8 (first_message_sequence_number record) ++
      encode_uint 8 (send_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (version_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (reserved_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_protocol_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (channel_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (session_id_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (payload_length_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (message_count_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (stream_offset_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (first_message_sequence_number_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (send_time_value, bytes) =>
                                              Some ({| version := version_value; reserved := reserved_value; message_protocol_id := message_protocol_id_value; channel_id := channel_id_value; session_id := session_id_value; payload_length := payload_length_value; message_count := message_count_value; stream_offset := stream_offset_value; first_message_sequence_number := first_message_sequence_number_value; send_time := send_time_value |}, bytes)
                                          end
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End IextpHeader.

  Module MessageHeader.

    (** IexTp message header *)
    Record t := {
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

End IexEquitiesIexTpHeaderV10.
