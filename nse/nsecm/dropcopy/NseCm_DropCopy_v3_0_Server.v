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
      - a Conversion rule
      - a Composite rule
      - a field read in bits
  *)

Module NseCmDropCopyV30Server.

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

  Module ResponseMessageHeader.

    (** RESPONSE_MESSAGE_HEADER, present once per packet however many messages are packed behind it *)
    Record t := {
      environment_type : list byte;
      compression_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (environment_type record) = 1 /\
      Datatypes.length (compression_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (environment_type record) ++
      encode_bytes 1 (compression_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (environment_type_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (compression_indicator_value, bytes) =>
              Some ({| environment_type := environment_type_value; compression_indicator := compression_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End ResponseMessageHeader.

  Module MessageHeader.

    (** MESSAGE_HEADER *)
    Record t := {
      transaction_code : N;
      error_code : N;
      sequence_number : N;
      message_length : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_code record < 256 ^ N.of_nat 2)%N /\
      (error_code record < 256 ^ N.of_nat 2)%N /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_length record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (transaction_code record) ++
      encode_uint 2 (error_code record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_length record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (transaction_code_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (error_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sequence_number_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (message_length_value, bytes) =>
                      Some ({| transaction_code := transaction_code_value; error_code := error_code_value; sequence_number := sequence_number_value; message_length := message_length_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End MessageHeader.

  Module IpDetailsPartitionWise.

    (** IP_DETAILS_PARTITION_WISE *)
    Record t := {
      ip_address : list byte;
      port : N;
      partition_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ip_address record) = 16 /\
      (port record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (partition_id record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (ip_address record) ++
      encode_uint 4 (port record) ++
      encode_bytes 6 (partition_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (ip_address_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (port_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (partition_id_value, bytes) =>
                  Some ({| ip_address := ip_address_value; port := port_value; partition_id := partition_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IpDetailsPartitionWise.

  Module GrResponseMessage.

    (** Returns the addresses of every partition the member must connect to, together with the session key and the cryptographic material for those connections *)
    Record t := {
      message_indicator : N;
      partition_count : N;
      ip_details_partition_wise : IpDetailsPartitionWise.t;
      session_key : list byte;
      cryptographic_key : list byte;
      cryptographic_iv : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_indicator record < 256 ^ N.of_nat 2)%N /\
      (partition_count record < 256 ^ N.of_nat 2)%N /\
      IpDetailsPartitionWise.bounded (ip_details_partition_wise record) /\
      Datatypes.length (session_key record) = 8 /\
      Datatypes.length (cryptographic_key record) = 32 /\
      Datatypes.length (cryptographic_iv record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_indicator record) ++
      encode_uint 2 (partition_count record) ++
      IpDetailsPartitionWise.encode (ip_details_partition_wise record) ++
      encode_bytes 8 (session_key record) ++
      encode_bytes 32 (cryptographic_key record) ++
      encode_bytes 16 (cryptographic_iv record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_indicator_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (partition_count_value, bytes) =>
              match IpDetailsPartitionWise.decode bytes with
              | None => None
              | Some (ip_details_partition_wise_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (session_key_value, bytes) =>
                      match decode_bytes 32 bytes with
                      | None => None
                      | Some (cryptographic_key_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (cryptographic_iv_value, bytes) =>
                              Some ({| message_indicator := message_indicator_value; partition_count := partition_count_value; ip_details_partition_wise := ip_details_partition_wise_value; session_key := session_key_value; cryptographic_key := cryptographic_key_value; cryptographic_iv := cryptographic_iv_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 86.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !IpDetailsPartitionWise.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite IpDetailsPartitionWise.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply IpDetailsPartitionWise.eq_dec]. Defined.

  End GrResponseMessage.

  Module DcSignonOutMessage.

    (** Confirms the logon, or terminates the connection when Error Code is set *)
    Record t := {
      user_id : N;
      partition_id : list byte;
      concurrent_login_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (user_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (partition_id record) = 6 /\
      (concurrent_login_id record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (user_id record) ++
      encode_bytes 6 (partition_id record) ++
      encode_uint 2 (concurrent_login_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (partition_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (concurrent_login_id_value, bytes) =>
                  Some ({| user_id := user_id_value; partition_id := partition_id_value; concurrent_login_id := concurrent_login_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcSignonOutMessage.

  Module DcErrorResponseTradeMessage.

    (** Rejects a trade only request, the reason given in the Error Code of the Message Header *)
    Record t := {
      error_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (error_message record) = 128.

    Definition encode (record : t) : list byte :=
      encode_bytes 128 (error_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 128 bytes with
      | None => None
      | Some (error_message_value, bytes) =>
          Some ({| error_message := error_message_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 128.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcErrorResponseTradeMessage.

  Module DcErrorResponseOrderMessage.

    (** Rejects an order and trade request, the reason given in the Error Code of the Message Header *)
    Record t := {
      error_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (error_message record) = 128.

    Definition encode (record : t) : list byte :=
      encode_bytes 128 (error_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 128 bytes with
      | None => None
      | Some (error_message_value, bytes) =>
          Some ({| error_message := error_message_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 128.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DcErrorResponseOrderMessage.

End NseCmDropCopyV30Server.
