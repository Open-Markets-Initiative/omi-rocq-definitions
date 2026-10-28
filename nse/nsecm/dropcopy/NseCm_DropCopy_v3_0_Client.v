From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd Drop Copy

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

Module NseCmDropCopyV30Client.

  Module PacketHeader.

    (** Drop copy twenty two byte packet header *)
    Record t := {
      packet_length : N;
      packet_sequence_number : N;
      checksum : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (checksum record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_uint 4 (packet_sequence_number record) ++
      encode_bytes 16 (checksum record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (packet_sequence_number_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (checksum_value, bytes) =>
                  Some ({| packet_length := packet_length_value; packet_sequence_number := packet_sequence_number_value; checksum := checksum_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module RequestMessageHeader.

    (** REQUEST_MESSAGE_HEADER *)
    Record t := {
      transaction_code : N;
      trader_id : N;
      request_sequence_number : N;
      partition_id : list byte;
      concurrent_login_id : N;
      func_indc : list byte;
      reserve : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_code record < 256 ^ N.of_nat 2)%N /\
      (trader_id record < 256 ^ N.of_nat 4)%N /\
      (request_sequence_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (partition_id record) = 6 /\
      (concurrent_login_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (func_indc record) = 1 /\
      (reserve record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (transaction_code record) ++
      encode_uint 4 (trader_id record) ++
      encode_uint 8 (request_sequence_number record) ++
      encode_bytes 6 (partition_id record) ++
      encode_uint 2 (concurrent_login_id record) ++
      encode_bytes 1 (func_indc record) ++
      encode_uint 1 (reserve record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (transaction_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trader_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_sequence_number_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (partition_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (concurrent_login_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (func_indc_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reserve_value, bytes) =>
                                  Some ({| transaction_code := transaction_code_value; trader_id := trader_id_value; request_sequence_number := request_sequence_number_value; partition_id := partition_id_value; concurrent_login_id := concurrent_login_id_value; func_indc := func_indc_value; reserve := reserve_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RequestMessageHeader.

  Module DcSignonInMessage.

    (** Logs the member on to a partition of the drop copy service *)
    Record t := {
      password : list byte;
      session_key : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (password record) = 8 /\
      Datatypes.length (session_key record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (password record) ++
      encode_bytes 8 (session_key record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (password_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (session_key_value, bytes) =>
              Some ({| password := password_value; session_key := session_key_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End DcSignonInMessage.

  Module DcTrdSubscriptionRequestMessage.

    (** Subscribes to the trade only drop copy on this partition from the named sequence number *)
    Record t := {
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          Some ({| sequence_number := sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End DcTrdSubscriptionRequestMessage.

  Module DcOntSubscriptionRequestMessage.

    (** Subscribes to the order and trade drop copy on this partition from the named sequence number *)
    Record t := {
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          Some ({| sequence_number := sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End DcOntSubscriptionRequestMessage.

End NseCmDropCopyV30Client.
