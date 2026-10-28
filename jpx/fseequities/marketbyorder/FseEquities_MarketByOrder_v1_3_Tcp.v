From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group Market By Order

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
      - a length prefix framing what follows
  *)

Module FseEquitiesMarketByOrderV13Tcp.

  Module TcpPacketHeader.

    (** Jpx Flex Tcp packet header carrying length prefix and packet type discriminator *)
    Record t := {
      packet_length : N;
      packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; packet_type := packet_type_value |}, bytes)
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

  End TcpPacketHeader.

  Module LoginRequestRetransmissionMessage.

    (** Tcp login request selecting retransmission, sent by the user. One of the two Packet Type codes the document gives the 18 byte Login Request. *)
    Record t := {
      user_id : list byte;
      multicast_group_number : N;
      number_of_system_reboots : N;
      sequence_number : N;
      requested_message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 6 /\
      (multicast_group_number record < 256 ^ N.of_nat 1)%N /\
      (number_of_system_reboots record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (requested_message_count record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_id record) ++
      encode_uint 1 (multicast_group_number record) ++
      encode_uint 1 (number_of_system_reboots record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 3 (requested_message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (multicast_group_number_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (number_of_system_reboots_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      match decode_uint 3 bytes with
                      | None => None
                      | Some (requested_message_count_value, bytes) =>
                          Some ({| user_id := user_id_value; multicast_group_number := multicast_group_number_value; number_of_system_reboots := number_of_system_reboots_value; sequence_number := sequence_number_value; requested_message_count := requested_message_count_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequestRetransmissionMessage.

  Module LoginRequestSnapshotMessage.

    (** Tcp login request selecting snapshot, sent by the user. Same layout as the retransmission request; Number of System Reboots, Sequence Number and Requested Message Count are all set to 0. *)
    Record t := {
      user_id : list byte;
      multicast_group_number : N;
      number_of_system_reboots : N;
      sequence_number : N;
      requested_message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 6 /\
      (multicast_group_number record < 256 ^ N.of_nat 1)%N /\
      (number_of_system_reboots record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (requested_message_count record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (user_id record) ++
      encode_uint 1 (multicast_group_number record) ++
      encode_uint 1 (number_of_system_reboots record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 3 (requested_message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (multicast_group_number_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (number_of_system_reboots_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      match decode_uint 3 bytes with
                      | None => None
                      | Some (requested_message_count_value, bytes) =>
                          Some ({| user_id := user_id_value; multicast_group_number := multicast_group_number_value; number_of_system_reboots := number_of_system_reboots_value; sequence_number := sequence_number_value; requested_message_count := requested_message_count_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequestSnapshotMessage.

  Module LoginResultAcceptedMessage.

    (** Tcp login response accepting the request. Result Code carries A. *)
    Record t := {
      multicast_group_number : N;
      result_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (multicast_group_number record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (result_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (multicast_group_number record) ++
      encode_bytes 1 (result_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (multicast_group_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (result_code_value, bytes) =>
              Some ({| multicast_group_number := multicast_group_number_value; result_code := result_code_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End LoginResultAcceptedMessage.

  Module LoginResultRejectedMessage.

    (** Tcp login response rejecting the request. Same layout as the accepted response; Result Code carries the reason the request failed. *)
    Record t := {
      multicast_group_number : N;
      result_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (multicast_group_number record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (result_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (multicast_group_number record) ++
      encode_bytes 1 (result_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (multicast_group_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (result_code_value, bytes) =>
              Some ({| multicast_group_number := multicast_group_number_value; result_code := result_code_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End LoginResultRejectedMessage.

  Module EndOfMessageMessage.

    (** Tcp end of message marker terminating a retransmission or snapshot session. *)
    Record t := {
      multicast_group_number : N;
      number_of_system_reboots : N;
      next_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (multicast_group_number record < 256 ^ N.of_nat 1)%N /\
      (number_of_system_reboots record < 256 ^ N.of_nat 1)%N /\
      (next_sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (multicast_group_number record) ++
      encode_uint 1 (number_of_system_reboots record) ++
      encode_uint 4 (next_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (multicast_group_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (number_of_system_reboots_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (next_sequence_number_value, bytes) =>
                  Some ({| multicast_group_number := multicast_group_number_value; number_of_system_reboots := number_of_system_reboots_value; next_sequence_number := next_sequence_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EndOfMessageMessage.

End FseEquitiesMarketByOrderV13Tcp.
