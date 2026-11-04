From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * CME Group iLink 3

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
      - a field present only on a condition
      - a block whose stated length holds more than its fields
      - a run counted by a field
      - a field read in bits

    License: MIT No Attribution
  *)

Module CmeGlobexILink3V86Server.

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

  Module MessageHeader.

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

  End MessageHeader.

  Module NegotiationReject.

    (** The Negotiation Reject message is sent when CME rejects a Negotiate message sent by the customer. *)
    Record t := {
      reason : list byte;
      uuid : N;
      request_timestamp : N;
      error_codes : N;
      fault_tolerance_indicator : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 48 /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (error_codes record < 256 ^ N.of_nat 2)%N /\
      (fault_tolerance_indicator record < 256 ^ N.of_nat 1)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 48 (reason record) ++
      encode_uint 8 (uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 2 (error_codes record) ++
      encode_uint 1 (fault_tolerance_indicator record) ++
      encode_uint 1 (split_msg record).

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
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (error_codes_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (fault_tolerance_indicator_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (split_msg_value, bytes) =>
                              Some ({| reason := reason_value; uuid := uuid_value; request_timestamp := request_timestamp_value; error_codes := error_codes_value; fault_tolerance_indicator := fault_tolerance_indicator_value; split_msg := split_msg_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NegotiationReject.

  Module EstablishmentAck.

    (** The Establishment Acknowledgment message is sent when an Establish message from a customer is accepted by CME. *)
    Record t := {
      uuid : N;
      request_timestamp : N;
      next_seq_no : N;
      previous_seq_no : N;
      previous_uuid : N;
      keep_alive_interval : N;
      secret_key_secure_id_expiration : N;
      fault_tolerance_indicator : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (next_seq_no record < 256 ^ N.of_nat 4)%N /\
      (previous_seq_no record < 256 ^ N.of_nat 4)%N /\
      (previous_uuid record < 256 ^ N.of_nat 8)%N /\
      (keep_alive_interval record < 256 ^ N.of_nat 2)%N /\
      (secret_key_secure_id_expiration record < 256 ^ N.of_nat 2)%N /\
      (fault_tolerance_indicator record < 256 ^ N.of_nat 1)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 4 (next_seq_no record) ++
      encode_uint 4 (previous_seq_no record) ++
      encode_uint 8 (previous_uuid record) ++
      encode_uint 2 (keep_alive_interval record) ++
      encode_uint 2 (secret_key_secure_id_expiration record) ++
      encode_uint 1 (fault_tolerance_indicator record) ++
      encode_uint 1 (split_msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (uuid_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (request_timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (next_seq_no_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (previous_seq_no_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (previous_uuid_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (keep_alive_interval_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (secret_key_secure_id_expiration_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (fault_tolerance_indicator_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (split_msg_value, bytes) =>
                                          Some ({| uuid := uuid_value; request_timestamp := request_timestamp_value; next_seq_no := next_seq_no_value; previous_seq_no := previous_seq_no_value; previous_uuid := previous_uuid_value; keep_alive_interval := keep_alive_interval_value; secret_key_secure_id_expiration := secret_key_secure_id_expiration_value; fault_tolerance_indicator := fault_tolerance_indicator_value; split_msg := split_msg_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EstablishmentAck.

  Module EstablishmentReject.

    (** The Establishment Reject message is sent when an Establish message from the customer is rejected by CME. *)
    Record t := {
      reason : list byte;
      uuid : N;
      request_timestamp : N;
      next_seq_no : N;
      error_codes : N;
      fault_tolerance_indicator : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 48 /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (next_seq_no record < 256 ^ N.of_nat 4)%N /\
      (error_codes record < 256 ^ N.of_nat 2)%N /\
      (fault_tolerance_indicator record < 256 ^ N.of_nat 1)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 48 (reason record) ++
      encode_uint 8 (uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 4 (next_seq_no record) ++
      encode_uint 2 (error_codes record) ++
      encode_uint 1 (fault_tolerance_indicator record) ++
      encode_uint 1 (split_msg record).

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
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (next_seq_no_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (error_codes_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (fault_tolerance_indicator_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (split_msg_value, bytes) =>
                                  Some ({| reason := reason_value; uuid := uuid_value; request_timestamp := request_timestamp_value; next_seq_no := next_seq_no_value; error_codes := error_codes_value; fault_tolerance_indicator := fault_tolerance_indicator_value; split_msg := split_msg_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
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
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EstablishmentReject.

  Module Sequence.

    (** The Sequence message is used in both Recoverable (CME to customer) and Idempotent (customer to CME) flows. *)
    Record t := {
      uuid : N;
      next_seq_no : N;
      fault_tolerance_indicator : N;
      keep_alive_interval_lapsed : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (next_seq_no record < 256 ^ N.of_nat 4)%N /\
      (fault_tolerance_indicator record < 256 ^ N.of_nat 1)%N /\
      (keep_alive_interval_lapsed record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (uuid record) ++
      encode_uint 4 (next_seq_no record) ++
      encode_uint 1 (fault_tolerance_indicator record) ++
      encode_uint 1 (keep_alive_interval_lapsed record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (uuid_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (next_seq_no_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (fault_tolerance_indicator_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (keep_alive_interval_lapsed_value, bytes) =>
                      Some ({| uuid := uuid_value; next_seq_no := next_seq_no_value; fault_tolerance_indicator := fault_tolerance_indicator_value; keep_alive_interval_lapsed := keep_alive_interval_lapsed_value |}, bytes)
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

  End Sequence.

  Module Terminate.

    (** The Terminate message is sent to indicate that the sender is going to disconnect the TCP socket connection. *)
    Record t := {
      reason : list byte;
      uuid : N;
      request_timestamp : N;
      error_codes : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 48 /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (error_codes record < 256 ^ N.of_nat 2)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 48 (reason record) ++
      encode_uint 8 (uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 2 (error_codes record) ++
      encode_uint 1 (split_msg record).

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
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (error_codes_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (split_msg_value, bytes) =>
                          Some ({| reason := reason_value; uuid := uuid_value; request_timestamp := request_timestamp_value; error_codes := error_codes_value; split_msg := split_msg_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
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

  Module Retransmission.

    (** The Retransmission message is sent when a Retransmit Request message from the customer is accepted by CME. *)
    Record t := {
      uuid : N;
      last_uuid : N;
      request_timestamp : N;
      from_seq_no : N;
      msg_count_16 : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (last_uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (from_seq_no record < 256 ^ N.of_nat 4)%N /\
      (msg_count_16 record < 256 ^ N.of_nat 2)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (uuid record) ++
      encode_uint 8 (last_uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 4 (from_seq_no record) ++
      encode_uint 2 (msg_count_16 record) ++
      encode_uint 1 (split_msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (uuid_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (last_uuid_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (from_seq_no_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (msg_count_16_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (split_msg_value, bytes) =>
                              Some ({| uuid := uuid_value; last_uuid := last_uuid_value; request_timestamp := request_timestamp_value; from_seq_no := from_seq_no_value; msg_count_16 := msg_count_16_value; split_msg := split_msg_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Retransmission.

  Module RetransmitReject.

    (** CME Globex sends a Retransmit Reject message when a Retransmit Request message from the customer is rejected. *)
    Record t := {
      reason : list byte;
      uuid : N;
      last_uuid : N;
      request_timestamp : N;
      error_codes : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 48 /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (last_uuid record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (error_codes record < 256 ^ N.of_nat 2)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 48 (reason record) ++
      encode_uint 8 (uuid record) ++
      encode_uint 8 (last_uuid record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 2 (error_codes record) ++
      encode_uint 1 (split_msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 48 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (uuid_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_uuid_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (request_timestamp_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (error_codes_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (split_msg_value, bytes) =>
                              Some ({| reason := reason_value; uuid := uuid_value; last_uuid := last_uuid_value; request_timestamp := request_timestamp_value; error_codes := error_codes_value; split_msg := split_msg_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 75.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmitReject.

  Module NotApplied.

    (** The Not Applied message is sent when CME detects a sequence gap from the customer. *)
    Record t := {
      uuid : N;
      from_seq_no : N;
      msg_count : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (uuid record < 256 ^ N.of_nat 8)%N /\
      (from_seq_no record < 256 ^ N.of_nat 4)%N /\
      (msg_count record < 256 ^ N.of_nat 4)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (uuid record) ++
      encode_uint 4 (from_seq_no record) ++
      encode_uint 4 (msg_count record) ++
      encode_uint 1 (split_msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (uuid_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (from_seq_no_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (msg_count_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (split_msg_value, bytes) =>
                      Some ({| uuid := uuid_value; from_seq_no := from_seq_no_value; msg_count := msg_count_value; split_msg := split_msg_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End NotApplied.

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

  Module BusinessReject.

    (** The Business Message Reject message can reject an application-level message, which fulfills session level rules but fails the business rules. *)
    Record t := {
      seq_num : N;
      uuid : N;
      text : list byte;
      sender_id_optional : list byte;
      party_details_list_req_id_optional : N;
      sending_time_epoch : N;
      business_reject_ref_id : N;
      location_optional : list byte;
      ref_seq_num : N;
      ref_tag_id : N;
      business_reject_reason : N;
      ref_msg_type : list byte;
      poss_retrans_flag : N;
      manual_order_indicator_optional : N;
      split_msg : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (text record) = 256 /\
      Datatypes.length (sender_id_optional record) = 20 /\
      (party_details_list_req_id_optional record < 256 ^ N.of_nat 8)%N /\
      (sending_time_epoch record < 256 ^ N.of_nat 8)%N /\
      (business_reject_ref_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (location_optional record) = 5 /\
      (ref_seq_num record < 256 ^ N.of_nat 4)%N /\
      (ref_tag_id record < 256 ^ N.of_nat 2)%N /\
      (business_reject_reason record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (ref_msg_type record) = 2 /\
      (poss_retrans_flag record < 256 ^ N.of_nat 1)%N /\
      (manual_order_indicator_optional record < 256 ^ N.of_nat 1)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (uuid record) ++
      encode_bytes 256 (text record) ++
      encode_bytes 20 (sender_id_optional record) ++
      encode_uint 8 (party_details_list_req_id_optional record) ++
      encode_uint 8 (sending_time_epoch record) ++
      encode_uint 8 (business_reject_ref_id record) ++
      encode_bytes 5 (location_optional record) ++
      encode_uint 4 (ref_seq_num record) ++
      encode_uint 2 (ref_tag_id record) ++
      encode_uint 2 (business_reject_reason record) ++
      encode_bytes 2 (ref_msg_type record) ++
      encode_uint 1 (poss_retrans_flag record) ++
      encode_uint 1 (manual_order_indicator_optional record) ++
      encode_uint 1 (split_msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seq_num_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (uuid_value, bytes) =>
              match decode_bytes 256 bytes with
              | None => None
              | Some (text_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (sender_id_optional_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (party_details_list_req_id_optional_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (sending_time_epoch_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (business_reject_ref_id_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (location_optional_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (ref_seq_num_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (ref_tag_id_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (business_reject_reason_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (ref_msg_type_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (poss_retrans_flag_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (manual_order_indicator_optional_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (split_msg_value, bytes) =>
                                                                  Some ({| seq_num := seq_num_value; uuid := uuid_value; text := text_value; sender_id_optional := sender_id_optional_value; party_details_list_req_id_optional := party_details_list_req_id_optional_value; sending_time_epoch := sending_time_epoch_value; business_reject_ref_id := business_reject_ref_id_value; location_optional := location_optional_value; ref_seq_num := ref_seq_num_value; ref_tag_id := ref_tag_id_value; business_reject_reason := business_reject_reason_value; ref_msg_type := ref_msg_type_value; poss_retrans_flag := poss_retrans_flag_value; manual_order_indicator_optional := manual_order_indicator_optional_value; split_msg := split_msg_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 330.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BusinessReject.

  Module CalculatedCcyLastQty.

    (** ExecutionReportTradeOutright *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End CalculatedCcyLastQty.

  Module GrossTradeAmt.

    (** ExecutionReportTradeOutright *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GrossTradeAmt.

  Module ContraGrossTradeAmt.

    (** Number of fills which comprise fill quantity *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ContraGrossTradeAmt.

  Module ContraCalculatedCcyLastQty.

    (** Number of fills which comprise fill quantity *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ContraCalculatedCcyLastQty.

  Module Volatility.

    (** ExecutionReportTradeSpreadLeg *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Volatility.

  Module OptionDelta.

    (** ExecutionReportTradeSpreadLeg *)
    Record t := {
      mantissa_32 : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa_32 record < 256 ^ N.of_nat 4)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (mantissa_32 record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (mantissa_32_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa_32 := mantissa_32_value; exponent := exponent_value |}, bytes)
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

  End OptionDelta.

  Module TimeToExpiration.

    (** ExecutionReportTradeSpreadLeg *)
    Record t := {
      mantissa_32 : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa_32 record < 256 ^ N.of_nat 4)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (mantissa_32 record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (mantissa_32_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa_32 := mantissa_32_value; exponent := exponent_value |}, bytes)
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

  End TimeToExpiration.

  Module RiskFreeRate.

    (** ExecutionReportTradeSpreadLeg *)
    Record t := {
      mantissa_32 : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa_32 record < 256 ^ N.of_nat 4)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (mantissa_32 record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (mantissa_32_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa_32 := mantissa_32_value; exponent := exponent_value |}, bytes)
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

  End RiskFreeRate.

  Module OrderCancelReject.

    (** The Order Cancel Reject message is issued upon receipt of a cancel request message which cannot be honored. *)
    Record t := {
      seq_num : N;
      uuid : N;
      text : list byte;
      exec_id : list byte;
      sender_id : list byte;
      cl_ord_id : list byte;
      party_details_list_req_id : N;
      order_id : N;
      transact_time : N;
      sending_time_epoch : N;
      order_request_id : N;
      location : list byte;
      cxl_rej_reason : N;
      delay_duration : N;
      manual_order_indicator : N;
      poss_retrans_flag : N;
      split_msg : N;
      liquidity_flag : N;
      delay_to_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (text record) = 256 /\
      Datatypes.length (exec_id record) = 40 /\
      Datatypes.length (sender_id record) = 20 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (party_details_list_req_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time_epoch record < 256 ^ N.of_nat 8)%N /\
      (order_request_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (location record) = 5 /\
      (cxl_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (delay_duration record < 256 ^ N.of_nat 2)%N /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (poss_retrans_flag record < 256 ^ N.of_nat 1)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N /\
      (liquidity_flag record < 256 ^ N.of_nat 1)%N /\
      (delay_to_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (uuid record) ++
      encode_bytes 256 (text record) ++
      encode_bytes 40 (exec_id record) ++
      encode_bytes 20 (sender_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (party_details_list_req_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (sending_time_epoch record) ++
      encode_uint 8 (order_request_id record) ++
      encode_bytes 5 (location record) ++
      encode_uint 2 (cxl_rej_reason record) ++
      encode_uint 2 (delay_duration record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_uint 1 (poss_retrans_flag record) ++
      encode_uint 1 (split_msg record) ++
      encode_uint 1 (liquidity_flag record) ++
      encode_uint 8 (delay_to_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seq_num_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (uuid_value, bytes) =>
              match decode_bytes 256 bytes with
              | None => None
              | Some (text_value, bytes) =>
                  match decode_bytes 40 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (sender_id_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (cl_ord_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (party_details_list_req_id_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (order_id_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (transact_time_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (sending_time_epoch_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (order_request_id_value, bytes) =>
                                                  match decode_bytes 5 bytes with
                                                  | None => None
                                                  | Some (location_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (cxl_rej_reason_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (delay_duration_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (manual_order_indicator_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (poss_retrans_flag_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (split_msg_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (liquidity_flag_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (delay_to_time_value, bytes) =>
                                                                                  Some ({| seq_num := seq_num_value; uuid := uuid_value; text := text_value; exec_id := exec_id_value; sender_id := sender_id_value; cl_ord_id := cl_ord_id_value; party_details_list_req_id := party_details_list_req_id_value; order_id := order_id_value; transact_time := transact_time_value; sending_time_epoch := sending_time_epoch_value; order_request_id := order_request_id_value; location := location_value; cxl_rej_reason := cxl_rej_reason_value; delay_duration := delay_duration_value; manual_order_indicator := manual_order_indicator_value; poss_retrans_flag := poss_retrans_flag_value; split_msg := split_msg_value; liquidity_flag := liquidity_flag_value; delay_to_time := delay_to_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 409.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelReject.

  Module OrderCancelReplaceReject.

    (** The Order Cancel Replace Reject message is issued upon receipt of a cancel replace request message that cannot be honored. *)
    Record t := {
      seq_num : N;
      uuid : N;
      text : list byte;
      exec_id : list byte;
      sender_id : list byte;
      cl_ord_id : list byte;
      party_details_list_req_id : N;
      order_id : N;
      transact_time : N;
      sending_time_epoch : N;
      order_request_id : N;
      location : list byte;
      cxl_rej_reason : N;
      delay_duration : N;
      manual_order_indicator : N;
      poss_retrans_flag : N;
      split_msg : N;
      liquidity_flag : N;
      delay_to_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (text record) = 256 /\
      Datatypes.length (exec_id record) = 40 /\
      Datatypes.length (sender_id record) = 20 /\
      Datatypes.length (cl_ord_id record) = 20 /\
      (party_details_list_req_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time_epoch record < 256 ^ N.of_nat 8)%N /\
      (order_request_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (location record) = 5 /\
      (cxl_rej_reason record < 256 ^ N.of_nat 2)%N /\
      (delay_duration record < 256 ^ N.of_nat 2)%N /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (poss_retrans_flag record < 256 ^ N.of_nat 1)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N /\
      (liquidity_flag record < 256 ^ N.of_nat 1)%N /\
      (delay_to_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (uuid record) ++
      encode_bytes 256 (text record) ++
      encode_bytes 40 (exec_id record) ++
      encode_bytes 20 (sender_id record) ++
      encode_bytes 20 (cl_ord_id record) ++
      encode_uint 8 (party_details_list_req_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (transact_time record) ++
      encode_uint 8 (sending_time_epoch record) ++
      encode_uint 8 (order_request_id record) ++
      encode_bytes 5 (location record) ++
      encode_uint 2 (cxl_rej_reason record) ++
      encode_uint 2 (delay_duration record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_uint 1 (poss_retrans_flag record) ++
      encode_uint 1 (split_msg record) ++
      encode_uint 1 (liquidity_flag record) ++
      encode_uint 8 (delay_to_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seq_num_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (uuid_value, bytes) =>
              match decode_bytes 256 bytes with
              | None => None
              | Some (text_value, bytes) =>
                  match decode_bytes 40 bytes with
                  | None => None
                  | Some (exec_id_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (sender_id_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (cl_ord_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (party_details_list_req_id_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (order_id_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (transact_time_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (sending_time_epoch_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (order_request_id_value, bytes) =>
                                                  match decode_bytes 5 bytes with
                                                  | None => None
                                                  | Some (location_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (cxl_rej_reason_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (delay_duration_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (manual_order_indicator_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (poss_retrans_flag_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (split_msg_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (liquidity_flag_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (delay_to_time_value, bytes) =>
                                                                                  Some ({| seq_num := seq_num_value; uuid := uuid_value; text := text_value; exec_id := exec_id_value; sender_id := sender_id_value; cl_ord_id := cl_ord_id_value; party_details_list_req_id := party_details_list_req_id_value; order_id := order_id_value; transact_time := transact_time_value; sending_time_epoch := sending_time_epoch_value; order_request_id := order_request_id_value; location := location_value; cxl_rej_reason := cxl_rej_reason_value; delay_duration := delay_duration_value; manual_order_indicator := manual_order_indicator_value; poss_retrans_flag := poss_retrans_flag_value; split_msg := split_msg_value; liquidity_flag := liquidity_flag_value; delay_to_time := delay_to_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 409.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderCancelReplaceReject.

  Module RequestForQuoteAck.

    (** Request for Quote Acknowledgment message is used in response to a Request for Quote message to either accept it or reject it. *)
    Record t := {
      seq_num : N;
      uuid : N;
      text : list byte;
      sender_id : list byte;
      exchange_quote_req_id : list byte;
      party_details_list_req_id : N;
      request_time : N;
      sending_time_epoch : N;
      quote_req_id : N;
      location : list byte;
      quote_reject_reason : N;
      delay_duration : N;
      quote_ack_status : N;
      manual_order_indicator : N;
      split_msg : N;
      poss_retrans_flag : N;
      delay_to_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (uuid record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (text record) = 256 /\
      Datatypes.length (sender_id record) = 20 /\
      Datatypes.length (exchange_quote_req_id record) = 17 /\
      (party_details_list_req_id record < 256 ^ N.of_nat 8)%N /\
      (request_time record < 256 ^ N.of_nat 8)%N /\
      (sending_time_epoch record < 256 ^ N.of_nat 8)%N /\
      (quote_req_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (location record) = 5 /\
      (quote_reject_reason record < 256 ^ N.of_nat 2)%N /\
      (delay_duration record < 256 ^ N.of_nat 2)%N /\
      (quote_ack_status record < 256 ^ N.of_nat 1)%N /\
      (manual_order_indicator record < 256 ^ N.of_nat 1)%N /\
      (split_msg record < 256 ^ N.of_nat 1)%N /\
      (poss_retrans_flag record < 256 ^ N.of_nat 1)%N /\
      (delay_to_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (uuid record) ++
      encode_bytes 256 (text record) ++
      encode_bytes 20 (sender_id record) ++
      encode_bytes 17 (exchange_quote_req_id record) ++
      encode_uint 8 (party_details_list_req_id record) ++
      encode_uint 8 (request_time record) ++
      encode_uint 8 (sending_time_epoch record) ++
      encode_uint 8 (quote_req_id record) ++
      encode_bytes 5 (location record) ++
      encode_uint 2 (quote_reject_reason record) ++
      encode_uint 2 (delay_duration record) ++
      encode_uint 1 (quote_ack_status record) ++
      encode_uint 1 (manual_order_indicator record) ++
      encode_uint 1 (split_msg record) ++
      encode_uint 1 (poss_retrans_flag record) ++
      encode_uint 8 (delay_to_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seq_num_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (uuid_value, bytes) =>
              match decode_bytes 256 bytes with
              | None => None
              | Some (text_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (sender_id_value, bytes) =>
                      match decode_bytes 17 bytes with
                      | None => None
                      | Some (exchange_quote_req_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (party_details_list_req_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (request_time_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (sending_time_epoch_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (quote_req_id_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (location_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (quote_reject_reason_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (delay_duration_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (quote_ack_status_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (manual_order_indicator_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (split_msg_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (poss_retrans_flag_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (delay_to_time_value, bytes) =>
                                                                          Some ({| seq_num := seq_num_value; uuid := uuid_value; text := text_value; sender_id := sender_id_value; exchange_quote_req_id := exchange_quote_req_id_value; party_details_list_req_id := party_details_list_req_id_value; request_time := request_time_value; sending_time_epoch := sending_time_epoch_value; quote_req_id := quote_req_id_value; location := location_value; quote_reject_reason := quote_reject_reason_value; delay_duration := delay_duration_value; quote_ack_status := quote_ack_status_value; manual_order_indicator := manual_order_indicator_value; split_msg := split_msg_value; poss_retrans_flag := poss_retrans_flag_value; delay_to_time := delay_to_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 358.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RequestForQuoteAck.

  Module MaturityMonthYear.

    (** SecurityDefinitionResponse *)
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

  Module LegOptionDelta.

    (** Up to 26 legs (i.e., repeating groups) supported for UDS for options. Up to 40 legs (i.e., repeating groups) supported for UDS for futures. Will be set to 0 for REPO *)
    Record t := {
      mantissa_32 : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa_32 record < 256 ^ N.of_nat 4)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (mantissa_32 record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (mantissa_32_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa_32 := mantissa_32_value; exponent := exponent_value |}, bytes)
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

  End LegOptionDelta.

End CmeGlobexILink3V86Server.
