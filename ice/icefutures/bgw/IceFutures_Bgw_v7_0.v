From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Intercontinental Exchange Binary Order Gateway

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
      - a field read in bits
      - a field present only on a condition
      - a block whose stated length holds more than its fields
      - a run counted by a field

    License: MIT No Attribution
  *)

Module IceFuturesBgwV70.

  Module SimpleOpenFramingHeader.

    (** Simple Open Framing Header *)
    Record t := {
      message_length : N;
      encoding_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (encoding_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 2 (encoding_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (encoding_type_value, bytes) =>
              Some ({| message_length := message_length_value; encoding_type := encoding_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SimpleOpenFramingHeader.

  Module FramingHeader.

    (** SimpleOpenFramingHeaderMessage *)
    Record t := {
      message_length : N;
      encoding_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (encoding_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 2 (encoding_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (encoding_type_value, bytes) =>
              Some ({| message_length := message_length_value; encoding_type := encoding_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End FramingHeader.

  Module SimpleOpenFramingHeaderMessage.

    (** SimpleOpenFramingHeaderMessage *)
    Record t := {
      framing_header : FramingHeader.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      FramingHeader.bounded (framing_header record).

    Definition encode (record : t) : list byte :=
      FramingHeader.encode (framing_header record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match FramingHeader.decode bytes with
      | None => None
      | Some (framing_header_value, bytes) =>
          Some ({| framing_header := framing_header_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !FramingHeader.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite FramingHeader.decode_encode by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply FramingHeader.eq_dec]. Defined.

  End SimpleOpenFramingHeaderMessage.

  Module LogonRequestMessage.

    (** LogonRequestMessage *)
    Record t := {
      user_id : list byte;
      client_id : N;
      heart_beat_interval : N;
      application_name : list byte;
      application_version : list byte;
      application_vendor : list byte;
      raw_data : list byte;
      ip_session_token : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 20 /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      (heart_beat_interval record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (application_name record) = 30 /\
      Datatypes.length (application_version record) = 50 /\
      Datatypes.length (application_vendor record) = 30 /\
      Datatypes.length (raw_data record) = 50 /\
      Datatypes.length (ip_session_token record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (user_id record) ++
      encode_uint 4 (client_id record) ++
      encode_uint 2 (heart_beat_interval record) ++
      encode_bytes 30 (application_name record) ++
      encode_bytes 50 (application_version record) ++
      encode_bytes 30 (application_vendor record) ++
      encode_bytes 50 (raw_data record) ++
      encode_bytes 50 (ip_session_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (client_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (heart_beat_interval_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (application_name_value, bytes) =>
                      match decode_bytes 50 bytes with
                      | None => None
                      | Some (application_version_value, bytes) =>
                          match decode_bytes 30 bytes with
                          | None => None
                          | Some (application_vendor_value, bytes) =>
                              match decode_bytes 50 bytes with
                              | None => None
                              | Some (raw_data_value, bytes) =>
                                  match decode_bytes 50 bytes with
                                  | None => None
                                  | Some (ip_session_token_value, bytes) =>
                                      Some ({| user_id := user_id_value; client_id := client_id_value; heart_beat_interval := heart_beat_interval_value; application_name := application_name_value; application_version := application_version_value; application_vendor := application_vendor_value; raw_data := raw_data_value; ip_session_token := ip_session_token_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 236.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonRequestMessage.

  Module LogonReportMessage.

    (** LogonReportMessage *)
    Record t := {
      user_id : list byte;
      heart_beat_interval : N;
      severity_level : N;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 20 /\
      (heart_beat_interval record < 256 ^ N.of_nat 2)%N /\
      (severity_level record < 256 ^ N.of_nat 1)%N /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (user_id record) ++
      encode_uint 2 (heart_beat_interval record) ++
      encode_uint 1 (severity_level record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (heart_beat_interval_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (severity_level_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (exchange_code_value, bytes) =>
                      match decode_bytes 100 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| user_id := user_id_value; heart_beat_interval := heart_beat_interval_value; severity_level := severity_level_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 127.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonReportMessage.

  Module LogoutRequestMessage.

    (** LogoutRequestMessage *)
    Record t := {
      user_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (user_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          Some ({| user_id := user_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End LogoutRequestMessage.

  Module LogoutReportMessage.

    (** LogoutReportMessage *)
    Record t := {
      user_id : list byte;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 20 /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (user_id record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (exchange_code_value, bytes) =>
              match decode_bytes 100 bytes with
              | None => None
              | Some (text_value, bytes) =>
                  Some ({| user_id := user_id_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 124.
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

  End LogoutReportMessage.

  Module ErrorMessage.

    (** ErrorMessage *)
    Record t := {
      ref_sequence_id : N;
      severity_level : N;
      supported_schema_version : list byte;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (ref_sequence_id record < 256 ^ N.of_nat 4)%N /\
      (severity_level record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (supported_schema_version record) = 20 /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (ref_sequence_id record) ++
      encode_uint 1 (severity_level record) ++
      encode_bytes 20 (supported_schema_version record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (ref_sequence_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (severity_level_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (supported_schema_version_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (exchange_code_value, bytes) =>
                      match decode_bytes 100 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| ref_sequence_id := ref_sequence_id_value; severity_level := severity_level_value; supported_schema_version := supported_schema_version_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 129.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ErrorMessage.

  Module GroupSizeEncoding.

    (** GroupSizeEncoding *)
    Record t := {
      block_length : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 2 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group := num_in_group_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End GroupSizeEncoding.

  Module SecurityDefinitionRejectMessage.

    (** SecurityDefinitionRejectMessage *)
    Record t := {
      security_req_id : N;
      security_response_type : N;
      security_request_type : N;
      market_type_id : N;
      security_type_optional : N;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_req_id record < 256 ^ N.of_nat 4)%N /\
      (security_response_type record < 256 ^ N.of_nat 1)%N /\
      (security_request_type record < 256 ^ N.of_nat 1)%N /\
      (market_type_id record < 256 ^ N.of_nat 4)%N /\
      (security_type_optional record < 256 ^ N.of_nat 1)%N /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_req_id record) ++
      encode_uint 1 (security_response_type record) ++
      encode_uint 1 (security_request_type record) ++
      encode_uint 4 (market_type_id record) ++
      encode_uint 1 (security_type_optional record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_req_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (security_response_type_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (security_request_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (market_type_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (security_type_optional_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (exchange_code_value, bytes) =>
                              match decode_bytes 100 bytes with
                              | None => None
                              | Some (text_value, bytes) =>
                                  Some ({| security_req_id := security_req_id_value; security_response_type := security_response_type_value; security_request_type := security_request_type_value; market_type_id := market_type_id_value; security_type_optional := security_type_optional_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 115.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityDefinitionRejectMessage.

  Module SecurityDefinitionRequestMessage.

    (** SecurityDefinitionRequestMessage *)
    Record t := {
      security_req_id : N;
      security_request_type : N;
      market_type_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_req_id record < 256 ^ N.of_nat 4)%N /\
      (security_request_type record < 256 ^ N.of_nat 1)%N /\
      (market_type_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_req_id record) ++
      encode_uint 1 (security_request_type record) ++
      encode_uint 4 (market_type_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_req_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (security_request_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (market_type_id_value, bytes) =>
                  Some ({| security_req_id := security_req_id_value; security_request_type := security_request_type_value; market_type_id := market_type_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SecurityDefinitionRequestMessage.

  Module TraderLogonRequestMessage.

    (** TraderLogonRequestMessage *)
    Record t := {
      originator_user_id : list byte;
      direct_electronic_access : N;
      trading_capacity : N;
      liquidity_provision : N;
      commodity_deriv_indicator : N;
      investment_decision : N;
      execution_decision : N;
      client_id_code : N;
      mifid_id : N;
      raw_data : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      (direct_electronic_access record < 256 ^ N.of_nat 1)%N /\
      (trading_capacity record < 256 ^ N.of_nat 1)%N /\
      (liquidity_provision record < 256 ^ N.of_nat 1)%N /\
      (commodity_deriv_indicator record < 256 ^ N.of_nat 1)%N /\
      (investment_decision record < 256 ^ N.of_nat 8)%N /\
      (execution_decision record < 256 ^ N.of_nat 8)%N /\
      (client_id_code record < 256 ^ N.of_nat 8)%N /\
      (mifid_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (raw_data record) = 50.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 1 (direct_electronic_access record) ++
      encode_uint 1 (trading_capacity record) ++
      encode_uint 1 (liquidity_provision record) ++
      encode_uint 1 (commodity_deriv_indicator record) ++
      encode_uint 8 (investment_decision record) ++
      encode_uint 8 (execution_decision record) ++
      encode_uint 8 (client_id_code record) ++
      encode_uint 8 (mifid_id record) ++
      encode_bytes 50 (raw_data record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (direct_electronic_access_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_capacity_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (liquidity_provision_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (commodity_deriv_indicator_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (investment_decision_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (execution_decision_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (client_id_code_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (mifid_id_value, bytes) =>
                                          match decode_bytes 50 bytes with
                                          | None => None
                                          | Some (raw_data_value, bytes) =>
                                              Some ({| originator_user_id := originator_user_id_value; direct_electronic_access := direct_electronic_access_value; trading_capacity := trading_capacity_value; liquidity_provision := liquidity_provision_value; commodity_deriv_indicator := commodity_deriv_indicator_value; investment_decision := investment_decision_value; execution_decision := execution_decision_value; client_id_code := client_id_code_value; mifid_id := mifid_id_value; raw_data := raw_data_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 106.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TraderLogonRequestMessage.

  Module TraderLogonReportMessage.

    (** TraderLogonReportMessage *)
    Record t := {
      originator_user_id : list byte;
      client_id : N;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      (client_id record < 256 ^ N.of_nat 4)%N /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 4 (client_id record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (client_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (exchange_code_value, bytes) =>
                  match decode_bytes 100 bytes with
                  | None => None
                  | Some (text_value, bytes) =>
                      Some ({| originator_user_id := originator_user_id_value; client_id := client_id_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 128.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TraderLogonReportMessage.

  Module TraderLogoutRequestMessage.

    (** TraderLogoutRequestMessage *)
    Record t := {
      originator_user_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          Some ({| originator_user_id := originator_user_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End TraderLogoutRequestMessage.

  Module TraderLogoutReportMessage.

    (** TraderLogoutReportMessage *)
    Record t := {
      originator_user_id : list byte;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (exchange_code_value, bytes) =>
              match decode_bytes 100 bytes with
              | None => None
              | Some (text_value, bytes) =>
                  Some ({| originator_user_id := originator_user_id_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 124.
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

  End TraderLogoutReportMessage.

  Module NewOrderRequestMessage.

    (** NewOrderRequestMessage *)
    Record t := {
      price_optional : N;
      order_qty : N;
      symbol : N;
      time_in_force : N;
      side : N;
      originator_user_id : list byte;
      ord_type : N;
      manual_order_indicator : N;
      cl_ord_id : N;
      max_show : N;
      stop_px : N;
      give_up_clearing_firm : N;
      clearing_firm : N;
      self_match_prevention_id : N;
      expire_date : N;
      self_match_prevention_instruction : list byte;
      exec_inst : list byte;
      direct_electronic_access : N;
      trading_capacity : N;
      liquidity_provision : N;
      commodity_deriv_indicator : N;
      investment_decision : N;
      execution_decision : N;
      client_id_code : N;
      mifid_id : N;
      cust_order_handling_inst : list byte;
      position_effect : list byte;
      alloc_handl_inst : list byte;
      price_type : N;
      clearing_account : list byte;
      customer_account_ref_id : list byte;
      memo : list byte;
      allocation_account : list byte;
      on_behalf_of_comp_id : list byte;
      on_behalf_of_sub_id : list byte;
      on_behalf_of_location_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (originator_user_id record) = 20 /\
      (ord_type record < 256 ^ N.of_nat 1)%N /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (max_show record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (give_up_clearing_firm record < 256 ^ N.of_nat 4)%N /\
      (clearing_firm record < 256 ^ N.of_nat 4)%N /\
      (self_match_prevention_id record < 256 ^ N.of_nat 8)%N /\
      (expire_date record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (self_match_prevention_instruction record) = 1 /\
      Datatypes.length (exec_inst record) = 1 /\
      (direct_electronic_access record < 256 ^ N.of_nat 1)%N /\
      (trading_capacity record < 256 ^ N.of_nat 1)%N /\
      (liquidity_provision record < 256 ^ N.of_nat 1)%N /\
      (commodity_deriv_indicator record < 256 ^ N.of_nat 1)%N /\
      (investment_decision record < 256 ^ N.of_nat 8)%N /\
      (execution_decision record < 256 ^ N.of_nat 8)%N /\
      (client_id_code record < 256 ^ N.of_nat 8)%N /\
      (mifid_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cust_order_handling_inst record) = 1 /\
      Datatypes.length (position_effect record) = 1 /\
      Datatypes.length (alloc_handl_inst record) = 1 /\
      (price_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_account record) = 14 /\
      Datatypes.length (customer_account_ref_id record) = 12 /\
      Datatypes.length (memo record) = 30 /\
      Datatypes.length (allocation_account record) = 20 /\
      Datatypes.length (on_behalf_of_comp_id record) = 41 /\
      Datatypes.length (on_behalf_of_sub_id record) = 41 /\
      Datatypes.length (on_behalf_of_location_id record) = 41.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (price_optional record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (side record) ++
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 1 (ord_type record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 8 (max_show record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 4 (give_up_clearing_firm record) ++
      encode_uint 4 (clearing_firm record) ++
      encode_uint 8 (self_match_prevention_id record) ++
      encode_uint 2 (expire_date record) ++
      encode_bytes 1 (self_match_prevention_instruction record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_uint 1 (direct_electronic_access record) ++
      encode_uint 1 (trading_capacity record) ++
      encode_uint 1 (liquidity_provision record) ++
      encode_uint 1 (commodity_deriv_indicator record) ++
      encode_uint 8 (investment_decision record) ++
      encode_uint 8 (execution_decision record) ++
      encode_uint 8 (client_id_code record) ++
      encode_uint 8 (mifid_id record) ++
      encode_bytes 1 (cust_order_handling_inst record) ++
      encode_bytes 1 (position_effect record) ++
      encode_bytes 1 (alloc_handl_inst record) ++
      encode_uint 1 (price_type record) ++
      encode_bytes 14 (clearing_account record) ++
      encode_bytes 12 (customer_account_ref_id record) ++
      encode_bytes 30 (memo record) ++
      encode_bytes 20 (allocation_account record) ++
      encode_bytes 41 (on_behalf_of_comp_id record) ++
      encode_bytes 41 (on_behalf_of_sub_id record) ++
      encode_bytes 41 (on_behalf_of_location_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (price_optional_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_qty_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (time_in_force_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (originator_user_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (ord_type_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (manual_order_indicator_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (max_show_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (stop_px_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (give_up_clearing_firm_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (clearing_firm_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (self_match_prevention_id_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (expire_date_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (self_match_prevention_instruction_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (exec_inst_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (direct_electronic_access_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (trading_capacity_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (liquidity_provision_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (commodity_deriv_indicator_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (investment_decision_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (execution_decision_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (client_id_code_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (mifid_id_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (cust_order_handling_inst_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (position_effect_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (alloc_handl_inst_value, bytes) =>
                                                                                                                      match decode_uint 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (price_type_value, bytes) =>
                                                                                                                          match decode_bytes 14 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (clearing_account_value, bytes) =>
                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (customer_account_ref_id_value, bytes) =>
                                                                                                                                  match decode_bytes 30 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (memo_value, bytes) =>
                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (allocation_account_value, bytes) =>
                                                                                                                                          match decode_bytes 41 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (on_behalf_of_comp_id_value, bytes) =>
                                                                                                                                              match decode_bytes 41 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (on_behalf_of_sub_id_value, bytes) =>
                                                                                                                                                  match decode_bytes 41 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (on_behalf_of_location_id_value, bytes) =>
                                                                                                                                                      Some ({| price_optional := price_optional_value; order_qty := order_qty_value; symbol := symbol_value; time_in_force := time_in_force_value; side := side_value; originator_user_id := originator_user_id_value; ord_type := ord_type_value; manual_order_indicator := manual_order_indicator_value; cl_ord_id := cl_ord_id_value; max_show := max_show_value; stop_px := stop_px_value; give_up_clearing_firm := give_up_clearing_firm_value; clearing_firm := clearing_firm_value; self_match_prevention_id := self_match_prevention_id_value; expire_date := expire_date_value; self_match_prevention_instruction := self_match_prevention_instruction_value; exec_inst := exec_inst_value; direct_electronic_access := direct_electronic_access_value; trading_capacity := trading_capacity_value; liquidity_provision := liquidity_provision_value; commodity_deriv_indicator := commodity_deriv_indicator_value; investment_decision := investment_decision_value; execution_decision := execution_decision_value; client_id_code := client_id_code_value; mifid_id := mifid_id_value; cust_order_handling_inst := cust_order_handling_inst_value; position_effect := position_effect_value; alloc_handl_inst := alloc_handl_inst_value; price_type := price_type_value; clearing_account := clearing_account_value; customer_account_ref_id := customer_account_ref_id_value; memo := memo_value; allocation_account := allocation_account_value; on_behalf_of_comp_id := on_behalf_of_comp_id_value; on_behalf_of_sub_id := on_behalf_of_sub_id_value; on_behalf_of_location_id := on_behalf_of_location_id_value |}, bytes)
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 327.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 bound_35]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderRequestMessage.

  Module CancelReplaceRequestMessage.

    (** CancelReplaceRequestMessage *)
    Record t := {
      price_optional : N;
      order_qty : N;
      symbol : N;
      time_in_force : N;
      side : N;
      originator_user_id : list byte;
      ord_type : N;
      manual_order_indicator : N;
      cl_ord_id : N;
      orig_cl_ord_id : N;
      max_show : N;
      stop_px : N;
      give_up_clearing_firm : N;
      clearing_firm : N;
      self_match_prevention_id : N;
      expire_date : N;
      self_match_prevention_instruction : list byte;
      exec_inst : list byte;
      direct_electronic_access : N;
      trading_capacity : N;
      liquidity_provision : N;
      commodity_deriv_indicator : N;
      investment_decision : N;
      execution_decision : N;
      client_id_code : N;
      mifid_id : N;
      alloc_handl_inst : list byte;
      price_type : N;
      clearing_account : list byte;
      customer_account_ref_id : list byte;
      memo : list byte;
      allocation_account : list byte;
      on_behalf_of_comp_id : list byte;
      on_behalf_of_sub_id : list byte;
      on_behalf_of_location_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (order_qty record < 256 ^ N.of_nat 8)%N /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (originator_user_id record) = 20 /\
      (ord_type record < 256 ^ N.of_nat 1)%N /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (orig_cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (max_show record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (give_up_clearing_firm record < 256 ^ N.of_nat 4)%N /\
      (clearing_firm record < 256 ^ N.of_nat 4)%N /\
      (self_match_prevention_id record < 256 ^ N.of_nat 8)%N /\
      (expire_date record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (self_match_prevention_instruction record) = 1 /\
      Datatypes.length (exec_inst record) = 1 /\
      (direct_electronic_access record < 256 ^ N.of_nat 1)%N /\
      (trading_capacity record < 256 ^ N.of_nat 1)%N /\
      (liquidity_provision record < 256 ^ N.of_nat 1)%N /\
      (commodity_deriv_indicator record < 256 ^ N.of_nat 1)%N /\
      (investment_decision record < 256 ^ N.of_nat 8)%N /\
      (execution_decision record < 256 ^ N.of_nat 8)%N /\
      (client_id_code record < 256 ^ N.of_nat 8)%N /\
      (mifid_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (alloc_handl_inst record) = 1 /\
      (price_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (clearing_account record) = 14 /\
      Datatypes.length (customer_account_ref_id record) = 12 /\
      Datatypes.length (memo record) = 30 /\
      Datatypes.length (allocation_account record) = 20 /\
      Datatypes.length (on_behalf_of_comp_id record) = 41 /\
      Datatypes.length (on_behalf_of_sub_id record) = 41 /\
      Datatypes.length (on_behalf_of_location_id record) = 41.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (price_optional record) ++
      encode_uint 8 (order_qty record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (side record) ++
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 1 (ord_type record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 8 (orig_cl_ord_id record) ++
      encode_uint 8 (max_show record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 4 (give_up_clearing_firm record) ++
      encode_uint 4 (clearing_firm record) ++
      encode_uint 8 (self_match_prevention_id record) ++
      encode_uint 2 (expire_date record) ++
      encode_bytes 1 (self_match_prevention_instruction record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_uint 1 (direct_electronic_access record) ++
      encode_uint 1 (trading_capacity record) ++
      encode_uint 1 (liquidity_provision record) ++
      encode_uint 1 (commodity_deriv_indicator record) ++
      encode_uint 8 (investment_decision record) ++
      encode_uint 8 (execution_decision record) ++
      encode_uint 8 (client_id_code record) ++
      encode_uint 8 (mifid_id record) ++
      encode_bytes 1 (alloc_handl_inst record) ++
      encode_uint 1 (price_type record) ++
      encode_bytes 14 (clearing_account record) ++
      encode_bytes 12 (customer_account_ref_id record) ++
      encode_bytes 30 (memo record) ++
      encode_bytes 20 (allocation_account record) ++
      encode_bytes 41 (on_behalf_of_comp_id record) ++
      encode_bytes 41 (on_behalf_of_sub_id record) ++
      encode_bytes 41 (on_behalf_of_location_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (price_optional_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_qty_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (time_in_force_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (originator_user_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (ord_type_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (manual_order_indicator_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (cl_ord_id_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (orig_cl_ord_id_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (max_show_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (stop_px_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (give_up_clearing_firm_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (clearing_firm_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (self_match_prevention_id_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (expire_date_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (self_match_prevention_instruction_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (exec_inst_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (direct_electronic_access_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trading_capacity_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (liquidity_provision_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (commodity_deriv_indicator_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (investment_decision_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (execution_decision_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (client_id_code_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (mifid_id_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (alloc_handl_inst_value, bytes) =>
                                                                                                                  match decode_uint 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (price_type_value, bytes) =>
                                                                                                                      match decode_bytes 14 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (clearing_account_value, bytes) =>
                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (customer_account_ref_id_value, bytes) =>
                                                                                                                              match decode_bytes 30 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (memo_value, bytes) =>
                                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (allocation_account_value, bytes) =>
                                                                                                                                      match decode_bytes 41 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (on_behalf_of_comp_id_value, bytes) =>
                                                                                                                                          match decode_bytes 41 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (on_behalf_of_sub_id_value, bytes) =>
                                                                                                                                              match decode_bytes 41 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (on_behalf_of_location_id_value, bytes) =>
                                                                                                                                                  Some ({| price_optional := price_optional_value; order_qty := order_qty_value; symbol := symbol_value; time_in_force := time_in_force_value; side := side_value; originator_user_id := originator_user_id_value; ord_type := ord_type_value; manual_order_indicator := manual_order_indicator_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; max_show := max_show_value; stop_px := stop_px_value; give_up_clearing_firm := give_up_clearing_firm_value; clearing_firm := clearing_firm_value; self_match_prevention_id := self_match_prevention_id_value; expire_date := expire_date_value; self_match_prevention_instruction := self_match_prevention_instruction_value; exec_inst := exec_inst_value; direct_electronic_access := direct_electronic_access_value; trading_capacity := trading_capacity_value; liquidity_provision := liquidity_provision_value; commodity_deriv_indicator := commodity_deriv_indicator_value; investment_decision := investment_decision_value; execution_decision := execution_decision_value; client_id_code := client_id_code_value; mifid_id := mifid_id_value; alloc_handl_inst := alloc_handl_inst_value; price_type := price_type_value; clearing_account := clearing_account_value; customer_account_ref_id := customer_account_ref_id_value; memo := memo_value; allocation_account := allocation_account_value; on_behalf_of_comp_id := on_behalf_of_comp_id_value; on_behalf_of_sub_id := on_behalf_of_sub_id_value; on_behalf_of_location_id := on_behalf_of_location_id_value |}, bytes)
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 333.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 bound_34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelReplaceRequestMessage.

  Module CancelRequestMessage.

    (** CancelRequestMessage *)
    Record t := {
      symbol : N;
      originator_user_id : list byte;
      cl_ord_id : N;
      orig_cl_ord_id : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (symbol record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (originator_user_id record) = 20 /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (orig_cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (symbol record) ++
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 8 (orig_cl_ord_id record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (originator_user_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (orig_cl_ord_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          Some ({| symbol := symbol_value; originator_user_id := originator_user_id_value; cl_ord_id := cl_ord_id_value; orig_cl_ord_id := orig_cl_ord_id_value; side := side_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelRequestMessage.

  Module QuoteRequestMessage.

    (** QuoteRequestMessage *)
    Record t := {
      originator_user_id : list byte;
      side_optional : N;
      order_qty_optional : N;
      rfq_req_id : N;
      symbol : N;
      clearing_firm_optional : N;
      clearing_account_optional : list byte;
      on_behalf_of_comp_id : list byte;
      on_behalf_of_sub_id : list byte;
      on_behalf_of_location_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      (side_optional record < 256 ^ N.of_nat 1)%N /\
      (order_qty_optional record < 256 ^ N.of_nat 8)%N /\
      (rfq_req_id record < 256 ^ N.of_nat 8)%N /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (clearing_firm_optional record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (clearing_account_optional record) = 14 /\
      Datatypes.length (on_behalf_of_comp_id record) = 41 /\
      Datatypes.length (on_behalf_of_sub_id record) = 41 /\
      Datatypes.length (on_behalf_of_location_id record) = 41.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 1 (side_optional record) ++
      encode_uint 8 (order_qty_optional record) ++
      encode_uint 8 (rfq_req_id record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 4 (clearing_firm_optional record) ++
      encode_bytes 14 (clearing_account_optional record) ++
      encode_bytes 41 (on_behalf_of_comp_id record) ++
      encode_bytes 41 (on_behalf_of_sub_id record) ++
      encode_bytes 41 (on_behalf_of_location_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (side_optional_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_qty_optional_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (rfq_req_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (clearing_firm_optional_value, bytes) =>
                              match decode_bytes 14 bytes with
                              | None => None
                              | Some (clearing_account_optional_value, bytes) =>
                                  match decode_bytes 41 bytes with
                                  | None => None
                                  | Some (on_behalf_of_comp_id_value, bytes) =>
                                      match decode_bytes 41 bytes with
                                      | None => None
                                      | Some (on_behalf_of_sub_id_value, bytes) =>
                                          match decode_bytes 41 bytes with
                                          | None => None
                                          | Some (on_behalf_of_location_id_value, bytes) =>
                                              Some ({| originator_user_id := originator_user_id_value; side_optional := side_optional_value; order_qty_optional := order_qty_optional_value; rfq_req_id := rfq_req_id_value; symbol := symbol_value; clearing_firm_optional := clearing_firm_optional_value; clearing_account_optional := clearing_account_optional_value; on_behalf_of_comp_id := on_behalf_of_comp_id_value; on_behalf_of_sub_id := on_behalf_of_sub_id_value; on_behalf_of_location_id := on_behalf_of_location_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 182.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRequestMessage.

  Module OrderMassCancelRequestMessage.

    (** OrderMassCancelRequestMessage *)
    Record t := {
      originator_user_id : list byte;
      ord_type_optional : N;
      side_optional : N;
      symbol_optional : N;
      cl_ord_id : N;
      market_type_i_d_optional : N;
      price_optional : N;
      mass_cancel_request_type : N;
      time_in_force_optional : N;
      on_behalf_of_sub_i_d_optional : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      (ord_type_optional record < 256 ^ N.of_nat 1)%N /\
      (side_optional record < 256 ^ N.of_nat 1)%N /\
      (symbol_optional record < 256 ^ N.of_nat 4)%N /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (market_type_i_d_optional record < 256 ^ N.of_nat 4)%N /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (mass_cancel_request_type record < 256 ^ N.of_nat 1)%N /\
      (time_in_force_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (on_behalf_of_sub_i_d_optional record) = 41.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 1 (ord_type_optional record) ++
      encode_uint 1 (side_optional record) ++
      encode_uint 4 (symbol_optional record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 4 (market_type_i_d_optional record) ++
      encode_uint 8 (price_optional record) ++
      encode_uint 1 (mass_cancel_request_type record) ++
      encode_uint 1 (time_in_force_optional record) ++
      encode_bytes 41 (on_behalf_of_sub_i_d_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (ord_type_optional_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_optional_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_optional_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (cl_ord_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (market_type_i_d_optional_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_optional_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (mass_cancel_request_type_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (time_in_force_optional_value, bytes) =>
                                          match decode_bytes 41 bytes with
                                          | None => None
                                          | Some (on_behalf_of_sub_i_d_optional_value, bytes) =>
                                              Some ({| originator_user_id := originator_user_id_value; ord_type_optional := ord_type_optional_value; side_optional := side_optional_value; symbol_optional := symbol_optional_value; cl_ord_id := cl_ord_id_value; market_type_i_d_optional := market_type_i_d_optional_value; price_optional := price_optional_value; mass_cancel_request_type := mass_cancel_request_type_value; time_in_force_optional := time_in_force_optional_value; on_behalf_of_sub_i_d_optional := on_behalf_of_sub_i_d_optional_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 89.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderMassCancelRequestMessage.

  Module SecurityDefinitionRequestCreateFlexMessage.

    (** SecurityDefinitionRequest_CreateFlexMessage *)
    Record t := {
      security_req_id : N;
      security_request_type : N;
      market_type_id : N;
      security_type : N;
      maturity_date : N;
      product_i_d_optional : N;
      symbol_optional : N;
      strike_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_req_id record < 256 ^ N.of_nat 4)%N /\
      (security_request_type record < 256 ^ N.of_nat 1)%N /\
      (market_type_id record < 256 ^ N.of_nat 4)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      (maturity_date record < 256 ^ N.of_nat 2)%N /\
      (product_i_d_optional record < 256 ^ N.of_nat 4)%N /\
      (symbol_optional record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_req_id record) ++
      encode_uint 1 (security_request_type record) ++
      encode_uint 4 (market_type_id record) ++
      encode_uint 1 (security_type record) ++
      encode_uint 2 (maturity_date record) ++
      encode_uint 4 (product_i_d_optional record) ++
      encode_uint 4 (symbol_optional record) ++
      encode_uint 8 (strike_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_req_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (security_request_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (market_type_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (security_type_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (maturity_date_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (product_i_d_optional_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (symbol_optional_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (strike_price_value, bytes) =>
                                      Some ({| security_req_id := security_req_id_value; security_request_type := security_request_type_value; market_type_id := market_type_id_value; security_type := security_type_value; maturity_date := maturity_date_value; product_i_d_optional := product_i_d_optional_value; symbol_optional := symbol_optional_value; strike_price := strike_price_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SecurityDefinitionRequestCreateFlexMessage.

  Module ExecIDOrderExecId.

    (** ExecutionReport_NewMessage *)
    Record t := {
      system_id : N;
      system_sequence_id : N;
      transact_time_utc_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (system_id record < 256 ^ N.of_nat 8)%N /\
      (system_sequence_id record < 256 ^ N.of_nat 4)%N /\
      (transact_time_utc_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (system_id record) ++
      encode_uint 4 (system_sequence_id record) ++
      encode_uint 8 (transact_time_utc_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (system_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (system_sequence_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transact_time_utc_timestamp_value, bytes) =>
                  Some ({| system_id := system_id_value; system_sequence_id := system_sequence_id_value; transact_time_utc_timestamp := transact_time_utc_timestamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End ExecIDOrderExecId.

  Module OrigOrderId.

    (** ExecutionReport_NewMessage *)
    Record t := {
      original_system_id : N;
      original_creation_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (original_system_id record < 256 ^ N.of_nat 8)%N /\
      (original_creation_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (original_system_id record) ++
      encode_uint 8 (original_creation_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (original_system_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (original_creation_timestamp_value, bytes) =>
              Some ({| original_system_id := original_system_id_value; original_creation_timestamp := original_creation_timestamp_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrigOrderId.

  Module ExecutionReportNewMessage.

    (** ExecutionReport_NewMessage *)
    Record t := {
      originator_user_id : list byte;
      exec_i_d_order_exec_id : ExecIDOrderExecId.t;
      cl_ord_id : N;
      symbol : N;
      ord_type : N;
      side : N;
      orig_order_id : OrigOrderId.t;
      leaves_qty : N;
      price_optional : N;
      me_acceptance_time : N;
      time_priority : N;
      order_status : N;
      memo : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      ExecIDOrderExecId.bounded (exec_i_d_order_exec_id record) /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (ord_type record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      OrigOrderId.bounded (orig_order_id record) /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (me_acceptance_time record < 256 ^ N.of_nat 8)%N /\
      (time_priority record < 256 ^ N.of_nat 8)%N /\
      (order_status record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (memo record) = 30.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      ExecIDOrderExecId.encode (exec_i_d_order_exec_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 1 (ord_type record) ++
      encode_uint 1 (side record) ++
      OrigOrderId.encode (orig_order_id record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (price_optional record) ++
      encode_uint 8 (me_acceptance_time record) ++
      encode_uint 8 (time_priority record) ++
      encode_uint 1 (order_status record) ++
      encode_bytes 30 (memo record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match ExecIDOrderExecId.decode bytes with
          | None => None
          | Some (exec_i_d_order_exec_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (ord_type_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match OrigOrderId.decode bytes with
                              | None => None
                              | Some (orig_order_id_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (leaves_qty_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (price_optional_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (me_acceptance_time_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (time_priority_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (order_status_value, bytes) =>
                                                      match decode_bytes 30 bytes with
                                                      | None => None
                                                      | Some (memo_value, bytes) =>
                                                          Some ({| originator_user_id := originator_user_id_value; exec_i_d_order_exec_id := exec_i_d_order_exec_id_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value; ord_type := ord_type_value; side := side_value; orig_order_id := orig_order_id_value; leaves_qty := leaves_qty_value; price_optional := price_optional_value; me_acceptance_time := me_acceptance_time_value; time_priority := time_priority_value; order_status := order_status_value; memo := memo_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 133.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecIDOrderExecId.encode_length, !encode_uint_length, !OrigOrderId.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ExecIDOrderExecId.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite OrigOrderId.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecIDOrderExecId.eq_dec | apply OrigOrderId.eq_dec]. Defined.

  End ExecutionReportNewMessage.

  Module ExecutionReportCancelMessage.

    (** ExecutionReport_CancelMessage *)
    Record t := {
      originator_user_id : list byte;
      exec_i_d_order_exec_id : ExecIDOrderExecId.t;
      cl_ord_id : N;
      symbol : N;
      ord_type : N;
      side : N;
      orig_order_id : OrigOrderId.t;
      orig_cl_ord_i_d_optional : N;
      me_acceptance_time : N;
      exchange_code : N;
      cancel_reason : N;
      cross_i_d_optional : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      ExecIDOrderExecId.bounded (exec_i_d_order_exec_id record) /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (ord_type record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      OrigOrderId.bounded (orig_order_id record) /\
      (orig_cl_ord_i_d_optional record < 256 ^ N.of_nat 8)%N /\
      (me_acceptance_time record < 256 ^ N.of_nat 8)%N /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      (cancel_reason record < 256 ^ N.of_nat 1)%N /\
      (cross_i_d_optional record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      ExecIDOrderExecId.encode (exec_i_d_order_exec_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 1 (ord_type record) ++
      encode_uint 1 (side record) ++
      OrigOrderId.encode (orig_order_id record) ++
      encode_uint 8 (orig_cl_ord_i_d_optional record) ++
      encode_uint 8 (me_acceptance_time record) ++
      encode_uint 4 (exchange_code record) ++
      encode_uint 1 (cancel_reason record) ++
      encode_uint 8 (cross_i_d_optional record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match ExecIDOrderExecId.decode bytes with
          | None => None
          | Some (exec_i_d_order_exec_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (ord_type_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match OrigOrderId.decode bytes with
                              | None => None
                              | Some (orig_order_id_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (orig_cl_ord_i_d_optional_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (me_acceptance_time_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (exchange_code_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (cancel_reason_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (cross_i_d_optional_value, bytes) =>
                                                      match decode_bytes 100 bytes with
                                                      | None => None
                                                      | Some (text_value, bytes) =>
                                                          Some ({| originator_user_id := originator_user_id_value; exec_i_d_order_exec_id := exec_i_d_order_exec_id_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value; ord_type := ord_type_value; side := side_value; orig_order_id := orig_order_id_value; orig_cl_ord_i_d_optional := orig_cl_ord_i_d_optional_value; me_acceptance_time := me_acceptance_time_value; exchange_code := exchange_code_value; cancel_reason := cancel_reason_value; cross_i_d_optional := cross_i_d_optional_value; text := text_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 199.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecIDOrderExecId.encode_length, !encode_uint_length, !OrigOrderId.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ExecIDOrderExecId.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite OrigOrderId.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecIDOrderExecId.eq_dec | apply OrigOrderId.eq_dec]. Defined.

  End ExecutionReportCancelMessage.

  Module ExecutionReportRejectMessage.

    (** ExecutionReport_RejectMessage *)
    Record t := {
      originator_user_id : list byte;
      exec_i_d_order_exec_id : ExecIDOrderExecId.t;
      cl_ord_id : N;
      symbol : N;
      ord_type_optional : N;
      side : N;
      orig_order_id : OrigOrderId.t;
      orig_cl_ord_i_d_optional : N;
      order_status : N;
      reject_response_to : N;
      reject_reason : N;
      exchange_code : N;
      memo : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      ExecIDOrderExecId.bounded (exec_i_d_order_exec_id record) /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (ord_type_optional record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      OrigOrderId.bounded (orig_order_id record) /\
      (orig_cl_ord_i_d_optional record < 256 ^ N.of_nat 8)%N /\
      (order_status record < 256 ^ N.of_nat 1)%N /\
      (reject_response_to record < 256 ^ N.of_nat 1)%N /\
      (reject_reason record < 256 ^ N.of_nat 1)%N /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (memo record) = 30 /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      ExecIDOrderExecId.encode (exec_i_d_order_exec_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 1 (ord_type_optional record) ++
      encode_uint 1 (side record) ++
      OrigOrderId.encode (orig_order_id record) ++
      encode_uint 8 (orig_cl_ord_i_d_optional record) ++
      encode_uint 1 (order_status record) ++
      encode_uint 1 (reject_response_to record) ++
      encode_uint 1 (reject_reason record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 30 (memo record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match ExecIDOrderExecId.decode bytes with
          | None => None
          | Some (exec_i_d_order_exec_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (ord_type_optional_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match OrigOrderId.decode bytes with
                              | None => None
                              | Some (orig_order_id_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (orig_cl_ord_i_d_optional_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (order_status_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (reject_response_to_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (reject_reason_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (exchange_code_value, bytes) =>
                                                      match decode_bytes 30 bytes with
                                                      | None => None
                                                      | Some (memo_value, bytes) =>
                                                          match decode_bytes 100 bytes with
                                                          | None => None
                                                          | Some (text_value, bytes) =>
                                                              Some ({| originator_user_id := originator_user_id_value; exec_i_d_order_exec_id := exec_i_d_order_exec_id_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value; ord_type_optional := ord_type_optional_value; side := side_value; orig_order_id := orig_order_id_value; orig_cl_ord_i_d_optional := orig_cl_ord_i_d_optional_value; order_status := order_status_value; reject_response_to := reject_response_to_value; reject_reason := reject_reason_value; exchange_code := exchange_code_value; memo := memo_value; text := text_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 215.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecIDOrderExecId.encode_length, !encode_uint_length, !OrigOrderId.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ExecIDOrderExecId.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite OrigOrderId.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecIDOrderExecId.eq_dec | apply OrigOrderId.eq_dec]. Defined.

  End ExecutionReportRejectMessage.

  Module ExecutionReportSnapshotMessage.

    (** ExecutionReport_SnapshotMessage *)
    Record t := {
      originator_user_id : list byte;
      exec_i_d_order_exec_id : ExecIDOrderExecId.t;
      cl_ord_id : N;
      symbol : N;
      ord_type : N;
      side : N;
      orig_order_id : OrigOrderId.t;
      max_show : N;
      leaves_qty : N;
      cum_qty : N;
      price_optional : N;
      stop_px : N;
      expire_date : N;
      time_priority : N;
      time_in_force : N;
      order_status : N;
      order_state : N;
      give_up_clearing_firm : N;
      clearing_firm_optional : N;
      direct_electronic_access : N;
      trading_capacity : N;
      liquidity_provision : N;
      commodity_deriv_indicator : N;
      investment_decision : N;
      execution_decision : N;
      client_id_code : N;
      mifid_id : N;
      self_match_prevention_id : N;
      self_match_prevention_instruction : list byte;
      manual_order_indicator : N;
      exec_inst : list byte;
      cust_order_handling_inst : list byte;
      position_effect : list byte;
      alloc_handl_inst : list byte;
      clearing_account_optional : list byte;
      customer_account_ref_id : list byte;
      memo : list byte;
      allocation_account : list byte;
      on_behalf_of_comp_id : list byte;
      on_behalf_of_sub_i_d_optional : list byte;
      on_behalf_of_location_i_d_optional : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      ExecIDOrderExecId.bounded (exec_i_d_order_exec_id record) /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (ord_type record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      OrigOrderId.bounded (orig_order_id record) /\
      (max_show record < 256 ^ N.of_nat 8)%N /\
      (leaves_qty record < 256 ^ N.of_nat 8)%N /\
      (cum_qty record < 256 ^ N.of_nat 8)%N /\
      (price_optional record < 256 ^ N.of_nat 8)%N /\
      (stop_px record < 256 ^ N.of_nat 8)%N /\
      (expire_date record < 256 ^ N.of_nat 2)%N /\
      (time_priority record < 256 ^ N.of_nat 8)%N /\
      (time_in_force record < 256 ^ N.of_nat 1)%N /\
      (order_status record < 256 ^ N.of_nat 1)%N /\
      (order_state record < 256 ^ N.of_nat 1)%N /\
      (give_up_clearing_firm record < 256 ^ N.of_nat 4)%N /\
      (clearing_firm_optional record < 256 ^ N.of_nat 4)%N /\
      (direct_electronic_access record < 256 ^ N.of_nat 1)%N /\
      (trading_capacity record < 256 ^ N.of_nat 1)%N /\
      (liquidity_provision record < 256 ^ N.of_nat 1)%N /\
      (commodity_deriv_indicator record < 256 ^ N.of_nat 1)%N /\
      (investment_decision record < 256 ^ N.of_nat 8)%N /\
      (execution_decision record < 256 ^ N.of_nat 8)%N /\
      (client_id_code record < 256 ^ N.of_nat 8)%N /\
      (mifid_id record < 256 ^ N.of_nat 8)%N /\
      (self_match_prevention_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (self_match_prevention_instruction record) = 1 /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exec_inst record) = 1 /\
      Datatypes.length (cust_order_handling_inst record) = 1 /\
      Datatypes.length (position_effect record) = 1 /\
      Datatypes.length (alloc_handl_inst record) = 1 /\
      Datatypes.length (clearing_account_optional record) = 14 /\
      Datatypes.length (customer_account_ref_id record) = 12 /\
      Datatypes.length (memo record) = 30 /\
      Datatypes.length (allocation_account record) = 20 /\
      Datatypes.length (on_behalf_of_comp_id record) = 41 /\
      Datatypes.length (on_behalf_of_sub_i_d_optional record) = 41 /\
      Datatypes.length (on_behalf_of_location_i_d_optional record) = 41.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      ExecIDOrderExecId.encode (exec_i_d_order_exec_id record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 1 (ord_type record) ++
      encode_uint 1 (side record) ++
      OrigOrderId.encode (orig_order_id record) ++
      encode_uint 8 (max_show record) ++
      encode_uint 8 (leaves_qty record) ++
      encode_uint 8 (cum_qty record) ++
      encode_uint 8 (price_optional record) ++
      encode_uint 8 (stop_px record) ++
      encode_uint 2 (expire_date record) ++
      encode_uint 8 (time_priority record) ++
      encode_uint 1 (time_in_force record) ++
      encode_uint 1 (order_status record) ++
      encode_uint 1 (order_state record) ++
      encode_uint 4 (give_up_clearing_firm record) ++
      encode_uint 4 (clearing_firm_optional record) ++
      encode_uint 1 (direct_electronic_access record) ++
      encode_uint 1 (trading_capacity record) ++
      encode_uint 1 (liquidity_provision record) ++
      encode_uint 1 (commodity_deriv_indicator record) ++
      encode_uint 8 (investment_decision record) ++
      encode_uint 8 (execution_decision record) ++
      encode_uint 8 (client_id_code record) ++
      encode_uint 8 (mifid_id record) ++
      encode_uint 8 (self_match_prevention_id record) ++
      encode_bytes 1 (self_match_prevention_instruction record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_bytes 1 (exec_inst record) ++
      encode_bytes 1 (cust_order_handling_inst record) ++
      encode_bytes 1 (position_effect record) ++
      encode_bytes 1 (alloc_handl_inst record) ++
      encode_bytes 14 (clearing_account_optional record) ++
      encode_bytes 12 (customer_account_ref_id record) ++
      encode_bytes 30 (memo record) ++
      encode_bytes 20 (allocation_account record) ++
      encode_bytes 41 (on_behalf_of_comp_id record) ++
      encode_bytes 41 (on_behalf_of_sub_i_d_optional record) ++
      encode_bytes 41 (on_behalf_of_location_i_d_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match ExecIDOrderExecId.decode bytes with
          | None => None
          | Some (exec_i_d_order_exec_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (ord_type_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match OrigOrderId.decode bytes with
                              | None => None
                              | Some (orig_order_id_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (max_show_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (leaves_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (cum_qty_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (price_optional_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (stop_px_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (expire_date_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (time_priority_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (time_in_force_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (order_status_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (order_state_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (give_up_clearing_firm_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (clearing_firm_optional_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (direct_electronic_access_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (trading_capacity_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (liquidity_provision_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (commodity_deriv_indicator_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (investment_decision_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (execution_decision_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (client_id_code_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (mifid_id_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (self_match_prevention_id_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (self_match_prevention_instruction_value, bytes) =>
                                                                                                                          match decode_uint 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (manual_order_indicator_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (exec_inst_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (cust_order_handling_inst_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (position_effect_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (alloc_handl_inst_value, bytes) =>
                                                                                                                                              match decode_bytes 14 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (clearing_account_optional_value, bytes) =>
                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (customer_account_ref_id_value, bytes) =>
                                                                                                                                                      match decode_bytes 30 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (memo_value, bytes) =>
                                                                                                                                                          match decode_bytes 20 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (allocation_account_value, bytes) =>
                                                                                                                                                              match decode_bytes 41 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (on_behalf_of_comp_id_value, bytes) =>
                                                                                                                                                                  match decode_bytes 41 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (on_behalf_of_sub_i_d_optional_value, bytes) =>
                                                                                                                                                                      match decode_bytes 41 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (on_behalf_of_location_i_d_optional_value, bytes) =>
                                                                                                                                                                          Some ({| originator_user_id := originator_user_id_value; exec_i_d_order_exec_id := exec_i_d_order_exec_id_value; cl_ord_id := cl_ord_id_value; symbol := symbol_value; ord_type := ord_type_value; side := side_value; orig_order_id := orig_order_id_value; max_show := max_show_value; leaves_qty := leaves_qty_value; cum_qty := cum_qty_value; price_optional := price_optional_value; stop_px := stop_px_value; expire_date := expire_date_value; time_priority := time_priority_value; time_in_force := time_in_force_value; order_status := order_status_value; order_state := order_state_value; give_up_clearing_firm := give_up_clearing_firm_value; clearing_firm_optional := clearing_firm_optional_value; direct_electronic_access := direct_electronic_access_value; trading_capacity := trading_capacity_value; liquidity_provision := liquidity_provision_value; commodity_deriv_indicator := commodity_deriv_indicator_value; investment_decision := investment_decision_value; execution_decision := execution_decision_value; client_id_code := client_id_code_value; mifid_id := mifid_id_value; self_match_prevention_id := self_match_prevention_id_value; self_match_prevention_instruction := self_match_prevention_instruction_value; manual_order_indicator := manual_order_indicator_value; exec_inst := exec_inst_value; cust_order_handling_inst := cust_order_handling_inst_value; position_effect := position_effect_value; alloc_handl_inst := alloc_handl_inst_value; clearing_account_optional := clearing_account_optional_value; customer_account_ref_id := customer_account_ref_id_value; memo := memo_value; allocation_account := allocation_account_value; on_behalf_of_comp_id := on_behalf_of_comp_id_value; on_behalf_of_sub_i_d_optional := on_behalf_of_sub_i_d_optional_value; on_behalf_of_location_i_d_optional := on_behalf_of_location_i_d_optional_value |}, bytes)
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 380.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ExecIDOrderExecId.encode_length, !encode_uint_length, !OrigOrderId.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 bound_40]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ExecIDOrderExecId.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite OrigOrderId.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExecIDOrderExecId.eq_dec | apply OrigOrderId.eq_dec]. Defined.

  End ExecutionReportSnapshotMessage.

  Module QuoteReportMessage.

    (** QuoteReportMessage *)
    Record t := {
      originator_user_id : list byte;
      side_optional : N;
      symbol : N;
      rfq_req_id : N;
      rfq_system_id : N;
      transact_time : N;
      order_qty_optional : N;
      quote_ack_status : N;
      quote_reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      (side_optional record < 256 ^ N.of_nat 1)%N /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (rfq_req_id record < 256 ^ N.of_nat 8)%N /\
      (rfq_system_id record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (order_qty_optional record < 256 ^ N.of_nat 8)%N /\
      (quote_ack_status record < 256 ^ N.of_nat 2)%N /\
      (quote_reject_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 1 (side_optional record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 8 (rfq_req_id record) ++
      encode_uint 8 (rfq_system_id record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (order_qty_optional record) ++
      encode_uint 2 (quote_ack_status record) ++
      encode_uint 1 (quote_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (side_optional_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (rfq_req_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (rfq_system_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (transact_time_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (order_qty_optional_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (quote_ack_status_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (quote_reject_reason_value, bytes) =>
                                          Some ({| originator_user_id := originator_user_id_value; side_optional := side_optional_value; symbol := symbol_value; rfq_req_id := rfq_req_id_value; rfq_system_id := rfq_system_id_value; transact_time := transact_time_value; order_qty_optional := order_qty_optional_value; quote_ack_status := quote_ack_status_value; quote_reject_reason := quote_reject_reason_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteReportMessage.

  Module NewOrderCrossReportMessage.

    (** NewOrderCrossReportMessage *)
    Record t := {
      originator_user_id : list byte;
      symbol : N;
      cross_id : N;
      transact_time : N;
      rfc_status : N;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      (symbol record < 256 ^ N.of_nat 4)%N /\
      (cross_id record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (rfc_status record < 256 ^ N.of_nat 1)%N /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 4 (symbol record) ++
      encode_uint 8 (cross_id record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 1 (rfc_status record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cross_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transact_time_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (rfc_status_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (exchange_code_value, bytes) =>
                              match decode_bytes 100 bytes with
                              | None => None
                              | Some (text_value, bytes) =>
                                  Some ({| originator_user_id := originator_user_id_value; symbol := symbol_value; cross_id := cross_id_value; transact_time := transact_time_value; rfc_status := rfc_status_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 145.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOrderCrossReportMessage.

  Module OrderMassCancelReportMessage.

    (** OrderMassCancelReportMessage *)
    Record t := {
      originator_user_id : list byte;
      symbol_optional : N;
      cl_ord_id : N;
      transact_time : N;
      market_type_i_d_optional : N;
      mass_cancel_request_type : N;
      mass_cancel_response : N;
      mass_cancel_reject_reason : N;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (originator_user_id record) = 20 /\
      (symbol_optional record < 256 ^ N.of_nat 4)%N /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (market_type_i_d_optional record < 256 ^ N.of_nat 4)%N /\
      (mass_cancel_request_type record < 256 ^ N.of_nat 1)%N /\
      (mass_cancel_response record < 256 ^ N.of_nat 1)%N /\
      (mass_cancel_reject_reason record < 256 ^ N.of_nat 1)%N /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (originator_user_id record) ++
      encode_uint 4 (symbol_optional record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 4 (market_type_i_d_optional record) ++
      encode_uint 1 (mass_cancel_request_type record) ++
      encode_uint 1 (mass_cancel_response record) ++
      encode_uint 1 (mass_cancel_reject_reason record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (originator_user_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_optional_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cl_ord_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transact_time_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (market_type_i_d_optional_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (mass_cancel_request_type_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (mass_cancel_response_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (mass_cancel_reject_reason_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (exchange_code_value, bytes) =>
                                          match decode_bytes 100 bytes with
                                          | None => None
                                          | Some (text_value, bytes) =>
                                              Some ({| originator_user_id := originator_user_id_value; symbol_optional := symbol_optional_value; cl_ord_id := cl_ord_id_value; transact_time := transact_time_value; market_type_i_d_optional := market_type_i_d_optional_value; mass_cancel_request_type := mass_cancel_request_type_value; mass_cancel_response := mass_cancel_response_value; mass_cancel_reject_reason := mass_cancel_reject_reason_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 151.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderMassCancelReportMessage.

  Module ResendRequestMessage.

    (** ResendRequestMessage *)
    Record t := {
      begin_seq_no : N;
      end_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_no record < 256 ^ N.of_nat 4)%N /\
      (end_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (begin_seq_no record) ++
      encode_uint 4 (end_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (begin_seq_no_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (end_seq_no_value, bytes) =>
              Some ({| begin_seq_no := begin_seq_no_value; end_seq_no := end_seq_no_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResendRequestMessage.

  Module ResendReportMessage.

    (** ResendReportMessage *)
    Record t := {
      begin_seq_no : N;
      end_seq_no : N;
      status : N;
      exchange_code : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_no record < 256 ^ N.of_nat 4)%N /\
      (end_seq_no record < 256 ^ N.of_nat 4)%N /\
      (status record < 256 ^ N.of_nat 1)%N /\
      (exchange_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (begin_seq_no record) ++
      encode_uint 4 (end_seq_no record) ++
      encode_uint 1 (status record) ++
      encode_uint 4 (exchange_code record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (begin_seq_no_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (end_seq_no_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (exchange_code_value, bytes) =>
                      match decode_bytes 100 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          Some ({| begin_seq_no := begin_seq_no_value; end_seq_no := end_seq_no_value; status := status_value; exchange_code := exchange_code_value; text := text_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 113.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ResendReportMessage.

  Module SequenceResetMessage.

    (** SequenceResetMessage *)
    Record t := {
      new_seq_no : N;
      gap_fill_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_seq_no record < 256 ^ N.of_nat 4)%N /\
      (gap_fill_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_seq_no record) ++
      encode_uint 1 (gap_fill_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_seq_no_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (gap_fill_flag_value, bytes) =>
              Some ({| new_seq_no := new_seq_no_value; gap_fill_flag := gap_fill_flag_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SequenceResetMessage.

End IceFuturesBgwV70.
