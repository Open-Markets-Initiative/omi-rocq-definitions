From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * CME Group Market Data Platform 3

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
      - the dispatch that chooses a message by its type
      - a field read in bits
      - a block whose stated length holds more than its fields
      - a run counted by a field

    License: MIT No Attribution
  *)

Module CmeGlobexMdp3V16Udp.

  Module BinaryPacketHeader.

    (** Cme Mdp Packet Header *)
    Record t := {
      packet_sequence_number : N;
      sending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (packet_sequence_number record) ++
      encode_uint 8 (sending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (packet_sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sending_time_value, bytes) =>
              Some ({| packet_sequence_number := packet_sequence_number_value; sending_time := sending_time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End BinaryPacketHeader.

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

  Module AdminLogin.

    (** AdminLogin *)
    Record t := {
      heart_bt_int : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (heart_bt_int record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (heart_bt_int record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (heart_bt_int_value, bytes) =>
          Some ({| heart_bt_int := heart_bt_int_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End AdminLogin.

  Module AdminLogout.

    (** AdminLogout *)
    Record t := {
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 100 bytes with
      | None => None
      | Some (text_value, bytes) =>
          Some ({| text := text_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 100.
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

  End AdminLogout.

  Module MaturityMonthYear.

    (** MDInstrumentDefinitionFuture *)
    Record t := {
      year : N;
      month : N;
      day : N;
      week : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (year record < 256 ^ N.of_nat 2)%N /\
      (month record < 256 ^ N.of_nat 1)%N /\
      (day record < 256 ^ N.of_nat 1)%N /\
      (week record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (year record) ++
      encode_uint 1 (month record) ++
      encode_uint 1 (day record) ++
      encode_uint 1 (week record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (year_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (month_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (day_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (week_value, bytes) =>
                      Some ({| year := year_value; month := month_value; day := day_value; week := week_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End MaturityMonthYear.

  Module GroupSize8Byte.

    (** 8 Byte aligned repeating group dimensions *)
    Record t := {
      block_length : N;
      padding_5 : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (padding_5 record < 256 ^ N.of_nat 5)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 5 (padding_5 record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 5 bytes with
          | None => None
          | Some (padding_5_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (num_in_group_value, bytes) =>
                  Some ({| block_length := block_length_value; padding_5 := padding_5_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSize8Byte.

  Module Negotiate.

    (** Negotiate *)
    Record t := {
      hmac_signature : list byte;
      access_key_id : list byte;
      uuid : N;
      request_timestamp : N;
      session : list byte;
      firm : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (hmac_signature record) = 32 /\
      Datatypes.length (access_key_id record) = 20 /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (session record) = 5 /\
      Datatypes.length (firm record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 32 (hmac_signature record) ++
      encode_bytes 20 (access_key_id record) ++
      encode_uint 8 (uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_bytes 5 (session record) ++
      encode_bytes 5 (firm record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 32 bytes with
      | None => None
      | Some (hmac_signature_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (access_key_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (uuid_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (request_timestamp_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (session_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (firm_value, bytes) =>
                              Some ({| hmac_signature := hmac_signature_value; access_key_id := access_key_id_value; uuid := uuid_value; request_timestamp := request_timestamp_value; session := session_value; firm := firm_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 78.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Negotiate.

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

End CmeGlobexMdp3V16Udp.
