From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * CME Group Session Management

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
      - the dispatch that chooses a message by its type
      - a block whose stated length holds more than its fields
      - a run counted by a field

    License: MIT No Attribution
  *)

Module CmeGlobexSessionMgmtV02Server.

  Module ServerTechnicalHeader.

    (** Cme Technical Header sent by Cme to the subscriber *)
    Record t := {
      encoding_type : N;
      message_sequence_number : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (encoding_type record < 256 ^ N.of_nat 2)%N /\
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (encoding_type record) ++
      encode_uint 4 (message_sequence_number record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (encoding_type_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (message_sequence_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  Some ({| encoding_type := encoding_type_value; message_sequence_number := message_sequence_number_value; sending_time := sending_time_value |}, bytes)
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

  End ServerTechnicalHeader.

  Module SimpleBinaryHeader.

    (** Template ID and length of message root *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (schema_id record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 2 (template_id record) ++
      encode_uint 2 (schema_id record) ++
      encode_uint 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End SimpleBinaryHeader.

  Module MessageHeader.

    (** Message Size followed by the Simple Binary Header *)
    Record t := {
      message_size : N;
      simple_binary_header : SimpleBinaryHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      SimpleBinaryHeader.bounded (simple_binary_header record).

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      SimpleBinaryHeader.encode (simple_binary_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match SimpleBinaryHeader.decode bytes with
          | None => None
          | Some (simple_binary_header_value, bytes) =>
              Some ({| message_size := message_size_value; simple_binary_header := simple_binary_header_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !SimpleBinaryHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite SimpleBinaryHeader.decode_encode by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply SimpleBinaryHeader.eq_dec]. Defined.

  End MessageHeader.

  Module NegotiationReject.

    (** NegotiationReject *)
    Record t := {
      reason : list byte;
      uuid : N;
      request_timestamp : N;
      error_codes : N;
      padding_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 48 /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (error_codes record < 256 ^ N.of_nat 1)%N /\
      (padding_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 48 (reason record) ++
      encode_uint 8 (uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 1 (error_codes record) ++
      encode_uint 5 (padding_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 48 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (uuid_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (error_codes_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (padding_5_value, bytes) =>
                          Some ({| reason := reason_value; uuid := uuid_value; request_timestamp := request_timestamp_value; error_codes := error_codes_value; padding_5 := padding_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 70.
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

  End NegotiationReject.

  Module NegotiationResponse.

    (** NegotiationResponse *)
    Record t := {
      uuid : N;
      request_timestamp : N;
      secret_key_secure_id_expiration : N;
      padding_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (secret_key_secure_id_expiration record < 256 ^ N.of_nat 2)%N /\
      (padding_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 2 (secret_key_secure_id_expiration record) ++
      encode_uint 4 (padding_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (uuid_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (request_timestamp_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (secret_key_secure_id_expiration_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (padding_4_value, bytes) =>
                      Some ({| uuid := uuid_value; request_timestamp := request_timestamp_value; secret_key_secure_id_expiration := secret_key_secure_id_expiration_value; padding_4 := padding_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End NegotiationResponse.

  Module Terminate.

    (** Terminate *)
    Record t := {
      reason : list byte;
      uuid : N;
      request_timestamp : N;
      error_codes : N;
      padding_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 48 /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (error_codes record < 256 ^ N.of_nat 1)%N /\
      (padding_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 48 (reason record) ++
      encode_uint 8 (uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 1 (error_codes record) ++
      encode_uint 5 (padding_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 48 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (uuid_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (error_codes_value, bytes) =>
                      match decode_uint 5 bytes with
                      | None => None
                      | Some (padding_5_value, bytes) =>
                          Some ({| reason := reason_value; uuid := uuid_value; request_timestamp := request_timestamp_value; error_codes := error_codes_value; padding_5 := padding_5_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 70.
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

  End Terminate.

  Module GroupSize.

    (** Repeating group dimensions *)
    Record t := {
      block_length : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group := num_in_group_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GroupSize.

  Module RequestReject.

    (** RequestReject *)
    Record t := {
      md_req_id_optional : N;
      md_req_rej_reason : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (md_req_id_optional record < 256 ^ N.of_nat 4)%N /\
      (md_req_rej_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (md_req_id_optional record) ++
      encode_uint 1 (md_req_rej_reason record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (md_req_id_optional_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (md_req_rej_reason_value, bytes) =>
              match decode_bytes 100 bytes with
              | None => None
              | Some (text_value, bytes) =>
                  Some ({| md_req_id_optional := md_req_id_optional_value; md_req_rej_reason := md_req_rej_reason_value; text := text_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
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

  End RequestReject.

End CmeGlobexSessionMgmtV02Server.
