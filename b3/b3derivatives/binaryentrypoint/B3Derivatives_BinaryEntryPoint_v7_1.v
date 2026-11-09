From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Brasil, Bolsa, Balcão Binary Entry Point

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

    License: MIT No Attribution
  *)

Module B3DerivativesBinaryEntryPointV71.

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

    (** B3 Sbe message header — message identifiers and length of message root *)
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

  Module NegotiateResponseMessage.

    (** NegotiateResponseMessage *)
    Record t := {
      session_id : N;
      session_ver_id : N;
      request_timestamp : N;
      entering_firm : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (session_ver_id record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (entering_firm record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 8 (session_ver_id record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 4 (entering_firm record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (session_ver_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (entering_firm_value, bytes) =>
                      Some ({| session_id := session_id_value; session_ver_id := session_ver_id_value; request_timestamp := request_timestamp_value; entering_firm := entering_firm_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End NegotiateResponseMessage.

  Module NegotiateRejectMessage.

    (** NegotiateRejectMessage *)
    Record t := {
      session_id : N;
      session_ver_id : N;
      request_timestamp : N;
      entering_firm_optional : N;
      negotiation_reject_code : N;
      offset_25_padding_3 : N;
      current_session_ver_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (session_ver_id record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (entering_firm_optional record < 256 ^ N.of_nat 4)%N /\
      (negotiation_reject_code record < 256 ^ N.of_nat 1)%N /\
      (offset_25_padding_3 record < 256 ^ N.of_nat 3)%N /\
      (current_session_ver_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 8 (session_ver_id record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 4 (entering_firm_optional record) ++
      encode_uint 1 (negotiation_reject_code record) ++
      encode_uint 3 (offset_25_padding_3 record) ++
      encode_uint 8 (current_session_ver_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (session_ver_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (entering_firm_optional_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (negotiation_reject_code_value, bytes) =>
                          match decode_uint 3 bytes with
                          | None => None
                          | Some (offset_25_padding_3_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (current_session_ver_id_value, bytes) =>
                                  Some ({| session_id := session_id_value; session_ver_id := session_ver_id_value; request_timestamp := request_timestamp_value; entering_firm_optional := entering_firm_optional_value; negotiation_reject_code := negotiation_reject_code_value; offset_25_padding_3 := offset_25_padding_3_value; current_session_ver_id := current_session_ver_id_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NegotiateRejectMessage.

  Module EstablishAckMessage.

    (** EstablishAckMessage *)
    Record t := {
      session_id : N;
      session_ver_id : N;
      request_timestamp : N;
      keep_alive_interval : N;
      next_seq_no : N;
      last_incoming_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (session_ver_id record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (keep_alive_interval record < 256 ^ N.of_nat 8)%N /\
      (next_seq_no record < 256 ^ N.of_nat 4)%N /\
      (last_incoming_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 8 (session_ver_id record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 8 (keep_alive_interval record) ++
      encode_uint 4 (next_seq_no record) ++
      encode_uint 4 (last_incoming_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (session_ver_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (keep_alive_interval_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (next_seq_no_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (last_incoming_seq_no_value, bytes) =>
                              Some ({| session_id := session_id_value; session_ver_id := session_ver_id_value; request_timestamp := request_timestamp_value; keep_alive_interval := keep_alive_interval_value; next_seq_no := next_seq_no_value; last_incoming_seq_no := last_incoming_seq_no_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End EstablishAckMessage.

  Module EstablishRejectMessage.

    (** EstablishRejectMessage *)
    Record t := {
      session_id : N;
      session_ver_id : N;
      request_timestamp : N;
      establishment_reject_code : N;
      offset_21_padding_1 : N;
      last_incoming_seq_no_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (session_ver_id record < 256 ^ N.of_nat 8)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (establishment_reject_code record < 256 ^ N.of_nat 1)%N /\
      (offset_21_padding_1 record < 256 ^ N.of_nat 1)%N /\
      (last_incoming_seq_no_optional record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 8 (session_ver_id record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 1 (establishment_reject_code record) ++
      encode_uint 1 (offset_21_padding_1 record) ++
      encode_uint 4 (last_incoming_seq_no_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (session_ver_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (request_timestamp_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (establishment_reject_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (offset_21_padding_1_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (last_incoming_seq_no_optional_value, bytes) =>
                              Some ({| session_id := session_id_value; session_ver_id := session_ver_id_value; request_timestamp := request_timestamp_value; establishment_reject_code := establishment_reject_code_value; offset_21_padding_1 := offset_21_padding_1_value; last_incoming_seq_no_optional := last_incoming_seq_no_optional_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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

  End EstablishRejectMessage.

  Module TerminateMessage.

    (** TerminateMessage *)
    Record t := {
      session_id : N;
      session_ver_id : N;
      termination_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (session_ver_id record < 256 ^ N.of_nat 8)%N /\
      (termination_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 8 (session_ver_id record) ++
      encode_uint 1 (termination_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (session_ver_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (termination_code_value, bytes) =>
                  Some ({| session_id := session_id_value; session_ver_id := session_ver_id_value; termination_code := termination_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End TerminateMessage.

  Module NotAppliedMessage.

    (** NotAppliedMessage *)
    Record t := {
      from_seq_no : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (from_seq_no record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (from_seq_no record) ++
      encode_uint 4 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (from_seq_no_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (count_value, bytes) =>
              Some ({| from_seq_no := from_seq_no_value; count := count_value |}, bytes)
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

  End NotAppliedMessage.

  Module SequenceMessage.

    (** SequenceMessage *)
    Record t := {
      next_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (next_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (next_seq_no_value, bytes) =>
          Some ({| next_seq_no := next_seq_no_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End SequenceMessage.

  Module RetransmitRequestMessage.

    (** RetransmitRequestMessage *)
    Record t := {
      session_id : N;
      timestamp : N;
      from_seq_no : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (from_seq_no record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (from_seq_no record) ++
      encode_uint 4 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (from_seq_no_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (count_value, bytes) =>
                      Some ({| session_id := session_id_value; timestamp := timestamp_value; from_seq_no := from_seq_no_value; count := count_value |}, bytes)
                  end
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

  End RetransmitRequestMessage.

  Module RetransmissionMessage.

    (** RetransmissionMessage *)
    Record t := {
      session_id : N;
      request_timestamp : N;
      next_seq_no : N;
      count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (next_seq_no record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 4 (next_seq_no record) ++
      encode_uint 4 (count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (request_timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (next_seq_no_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (count_value, bytes) =>
                      Some ({| session_id := session_id_value; request_timestamp := request_timestamp_value; next_seq_no := next_seq_no_value; count := count_value |}, bytes)
                  end
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

  End RetransmissionMessage.

  Module RetransmitRejectMessage.

    (** RetransmitRejectMessage *)
    Record t := {
      session_id : N;
      request_timestamp : N;
      retransmit_reject_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (request_timestamp record < 256 ^ N.of_nat 8)%N /\
      (retransmit_reject_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 8 (request_timestamp record) ++
      encode_uint 1 (retransmit_reject_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (request_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (retransmit_reject_code_value, bytes) =>
                  Some ({| session_id := session_id_value; request_timestamp := request_timestamp_value; retransmit_reject_code := retransmit_reject_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End RetransmitRejectMessage.

  Module InboundBusinessHeader.

    (** InboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      market_segment_id : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (market_segment_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (market_segment_id record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; market_segment_id := market_segment_id_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End InboundBusinessHeader.

  Module InvestorId.

    (** SimpleNewOrderMessage *)
    Record t := {
      prefix : N;
      offset_2_padding_2 : N;
      document : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (prefix record < 256 ^ N.of_nat 2)%N /\
      (offset_2_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (document record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (prefix record) ++
      encode_uint 2 (offset_2_padding_2 record) ++
      encode_uint 4 (document record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (prefix_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_2_padding_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (document_value, bytes) =>
                  Some ({| prefix := prefix_value; offset_2_padding_2 := offset_2_padding_2_value; document := document_value |}, bytes)
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

  End InvestorId.

  Module CustodianInfo.

    (** NewOrderSingleMessage *)
    Record t := {
      custodian : N;
      custody_account : N;
      custody_allocation_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (custodian record < 256 ^ N.of_nat 4)%N /\
      (custody_account record < 256 ^ N.of_nat 4)%N /\
      (custody_allocation_type record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (custodian record) ++
      encode_uint 4 (custody_account record) ++
      encode_uint 4 (custody_allocation_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (custodian_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (custody_account_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (custody_allocation_type_value, bytes) =>
                  Some ({| custodian := custodian_value; custody_account := custody_account_value; custody_allocation_type := custody_allocation_type_value |}, bytes)
              end
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

  End CustodianInfo.

  Module GroupSizeEncoding.

    (** GroupSizeEncoding *)
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

  End GroupSizeEncoding.

  Module OutboundBusinessHeader.

    (** OutboundBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      padding : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_bytes 1 (padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (padding_value, bytes) =>
                          Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; padding := padding_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End OutboundBusinessHeader.

  Module SecurityDefinitionResponseMessage.

    (** SecurityDefinitionResponseMessage *)
    Record t := {
      outbound_business_header : OutboundBusinessHeader.t;
      offset_18_padding_2 : N;
      security_req_id : N;
      security_id : N;
      security_response_type : N;
      security_strategy_type : list byte;
      symbol : list byte;
      security_response_id : N;
      sender_location : list byte;
      entering_trader : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutboundBusinessHeader.bounded (outbound_business_header record) /\
      (offset_18_padding_2 record < 256 ^ N.of_nat 2)%N /\
      (security_req_id record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (security_response_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_strategy_type record) = 3 /\
      Datatypes.length (symbol record) = 20 /\
      (security_response_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sender_location record) = 10 /\
      Datatypes.length (entering_trader record) = 5.

    Definition encode (record : t) : list byte :=
      OutboundBusinessHeader.encode (outbound_business_header record) ++
      encode_uint 2 (offset_18_padding_2 record) ++
      encode_uint 8 (security_req_id record) ++
      encode_uint 8 (security_id record) ++
      encode_uint 1 (security_response_type record) ++
      encode_bytes 3 (security_strategy_type record) ++
      encode_bytes 20 (symbol record) ++
      encode_uint 8 (security_response_id record) ++
      encode_bytes 10 (sender_location record) ++
      encode_bytes 5 (entering_trader record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutboundBusinessHeader.decode bytes with
      | None => None
      | Some (outbound_business_header_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (offset_18_padding_2_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (security_req_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (security_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (security_response_type_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (security_strategy_type_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (symbol_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (security_response_id_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (sender_location_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (entering_trader_value, bytes) =>
                                              Some ({| outbound_business_header := outbound_business_header_value; offset_18_padding_2 := offset_18_padding_2_value; security_req_id := security_req_id_value; security_id := security_id_value; security_response_type := security_response_type_value; security_strategy_type := security_strategy_type_value; symbol := symbol_value; security_response_id := security_response_id_value; sender_location := sender_location_value; entering_trader := entering_trader_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 83.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutboundBusinessHeader.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutboundBusinessHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutboundBusinessHeader.eq_dec]. Defined.

  End SecurityDefinitionResponseMessage.

  Module BidirectionalBusinessHeader.

    (** BidirectionalBusinessHeader *)
    Record t := {
      session_id : N;
      msg_seq_num : N;
      sending_time : N;
      poss_resend : N;
      market_segment_id_optional : N;
      padding_char_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_id record < 256 ^ N.of_nat 4)%N /\
      (msg_seq_num record < 256 ^ N.of_nat 4)%N /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (poss_resend record < 256 ^ N.of_nat 1)%N /\
      (market_segment_id_optional record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (padding_char_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (session_id record) ++
      encode_uint 4 (msg_seq_num record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 1 (poss_resend record) ++
      encode_uint 1 (market_segment_id_optional record) ++
      encode_bytes 2 (padding_char_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (session_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (msg_seq_num_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sending_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (poss_resend_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (market_segment_id_optional_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (padding_char_2_value, bytes) =>
                              Some ({| session_id := session_id_value; msg_seq_num := msg_seq_num_value; sending_time := sending_time_value; poss_resend := poss_resend_value; market_segment_id_optional := market_segment_id_optional_value; padding_char_2 := padding_char_2_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidirectionalBusinessHeader.

  Module PositionMaintenanceCancelRequestMessage.

    (** PositionMaintenanceCancelRequestMessage *)
    Record t := {
      inbound_business_header : InboundBusinessHeader.t;
      pos_req_id : N;
      security_id : N;
      orig_pos_req_ref_id : N;
      pos_maint_rpt_ref_id : N;
      sender_location : list byte;
      entering_trader : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InboundBusinessHeader.bounded (inbound_business_header record) /\
      (pos_req_id record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (orig_pos_req_ref_id record < 256 ^ N.of_nat 8)%N /\
      (pos_maint_rpt_ref_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sender_location record) = 10 /\
      Datatypes.length (entering_trader record) = 5.

    Definition encode (record : t) : list byte :=
      InboundBusinessHeader.encode (inbound_business_header record) ++
      encode_uint 8 (pos_req_id record) ++
      encode_uint 8 (security_id record) ++
      encode_uint 8 (orig_pos_req_ref_id record) ++
      encode_uint 8 (pos_maint_rpt_ref_id record) ++
      encode_bytes 10 (sender_location record) ++
      encode_bytes 5 (entering_trader record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InboundBusinessHeader.decode bytes with
      | None => None
      | Some (inbound_business_header_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (pos_req_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (orig_pos_req_ref_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (pos_maint_rpt_ref_id_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (sender_location_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (entering_trader_value, bytes) =>
                                  Some ({| inbound_business_header := inbound_business_header_value; pos_req_id := pos_req_id_value; security_id := security_id_value; orig_pos_req_ref_id := orig_pos_req_ref_id_value; pos_maint_rpt_ref_id := pos_maint_rpt_ref_id_value; sender_location := sender_location_value; entering_trader := entering_trader_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InboundBusinessHeader.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InboundBusinessHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InboundBusinessHeader.eq_dec]. Defined.

  End PositionMaintenanceCancelRequestMessage.

  Module AllocationReportMessage.

    (** AllocationReportMessage *)
    Record t := {
      outbound_business_header : OutboundBusinessHeader.t;
      alloc_id : N;
      security_id : N;
      alloc_report_id : N;
      alloc_trans_type : list byte;
      alloc_report_type : list byte;
      alloc_no_orders_type : list byte;
      alloc_rej_code : N;
      quantity : N;
      alloc_status : list byte;
      trade_date_optional : N;
      transact_time : N;
      side : list byte;
      sender_location : list byte;
      entering_trader : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OutboundBusinessHeader.bounded (outbound_business_header record) /\
      (alloc_id record < 256 ^ N.of_nat 8)%N /\
      (security_id record < 256 ^ N.of_nat 8)%N /\
      (alloc_report_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (alloc_trans_type record) = 1 /\
      Datatypes.length (alloc_report_type record) = 1 /\
      Datatypes.length (alloc_no_orders_type record) = 1 /\
      (alloc_rej_code record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (alloc_status record) = 1 /\
      (trade_date_optional record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (sender_location record) = 10 /\
      Datatypes.length (entering_trader record) = 5.

    Definition encode (record : t) : list byte :=
      OutboundBusinessHeader.encode (outbound_business_header record) ++
      encode_uint 8 (alloc_id record) ++
      encode_uint 8 (security_id record) ++
      encode_uint 8 (alloc_report_id record) ++
      encode_bytes 1 (alloc_trans_type record) ++
      encode_bytes 1 (alloc_report_type record) ++
      encode_bytes 1 (alloc_no_orders_type record) ++
      encode_uint 4 (alloc_rej_code record) ++
      encode_uint 8 (quantity record) ++
      encode_bytes 1 (alloc_status record) ++
      encode_uint 2 (trade_date_optional record) ++
      encode_uint 8 (transact_time record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 10 (sender_location record) ++
      encode_bytes 5 (entering_trader record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OutboundBusinessHeader.decode bytes with
      | None => None
      | Some (outbound_business_header_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (alloc_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (security_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (alloc_report_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (alloc_trans_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (alloc_report_type_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (alloc_no_orders_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (alloc_rej_code_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (quantity_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (alloc_status_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (trade_date_optional_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (transact_time_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (side_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (sender_location_value, bytes) =>
                                                              match decode_bytes 5 bytes with
                                                              | None => None
                                                              | Some (entering_trader_value, bytes) =>
                                                                  Some ({| outbound_business_header := outbound_business_header_value; alloc_id := alloc_id_value; security_id := security_id_value; alloc_report_id := alloc_report_id_value; alloc_trans_type := alloc_trans_type_value; alloc_report_type := alloc_report_type_value; alloc_no_orders_type := alloc_no_orders_type_value; alloc_rej_code := alloc_rej_code_value; quantity := quantity_value; alloc_status := alloc_status_value; trade_date_optional := trade_date_optional_value; transact_time := transact_time_value; side := side_value; sender_location := sender_location_value; entering_trader := entering_trader_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 84.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OutboundBusinessHeader.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OutboundBusinessHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply OutboundBusinessHeader.eq_dec]. Defined.

  End AllocationReportMessage.

  Module OrderMassActionRequestMessage.

    (** OrderMassActionRequestMessage *)
    Record t := {
      inbound_business_header : InboundBusinessHeader.t;
      mass_action_type : N;
      mass_action_scope : N;
      cl_ord_id : N;
      mass_cancel_restatement_reason : N;
      ord_tag_id : N;
      side_optional : list byte;
      offset_31_padding_1 : N;
      asset : list byte;
      security_id_optional : N;
      action_target_session_id : N;
      action_target_group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InboundBusinessHeader.bounded (inbound_business_header record) /\
      (mass_action_type record < 256 ^ N.of_nat 1)%N /\
      (mass_action_scope record < 256 ^ N.of_nat 1)%N /\
      (cl_ord_id record < 256 ^ N.of_nat 8)%N /\
      (mass_cancel_restatement_reason record < 256 ^ N.of_nat 1)%N /\
      (ord_tag_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (side_optional record) = 1 /\
      (offset_31_padding_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (asset record) = 6 /\
      (security_id_optional record < 256 ^ N.of_nat 8)%N /\
      (action_target_session_id record < 256 ^ N.of_nat 4)%N /\
      (action_target_group_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      InboundBusinessHeader.encode (inbound_business_header record) ++
      encode_uint 1 (mass_action_type record) ++
      encode_uint 1 (mass_action_scope record) ++
      encode_uint 8 (cl_ord_id record) ++
      encode_uint 1 (mass_cancel_restatement_reason record) ++
      encode_uint 1 (ord_tag_id record) ++
      encode_bytes 1 (side_optional record) ++
      encode_uint 1 (offset_31_padding_1 record) ++
      encode_bytes 6 (asset record) ++
      encode_uint 8 (security_id_optional record) ++
      encode_uint 4 (action_target_session_id record) ++
      encode_uint 4 (action_target_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InboundBusinessHeader.decode bytes with
      | None => None
      | Some (inbound_business_header_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (mass_action_type_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (mass_action_scope_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cl_ord_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (mass_cancel_restatement_reason_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (ord_tag_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_optional_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (offset_31_padding_1_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (asset_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (security_id_optional_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (action_target_session_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (action_target_group_id_value, bytes) =>
                                                      Some ({| inbound_business_header := inbound_business_header_value; mass_action_type := mass_action_type_value; mass_action_scope := mass_action_scope_value; cl_ord_id := cl_ord_id_value; mass_cancel_restatement_reason := mass_cancel_restatement_reason_value; ord_tag_id := ord_tag_id_value; side_optional := side_optional_value; offset_31_padding_1 := offset_31_padding_1_value; asset := asset_value; security_id_optional := security_id_optional_value; action_target_session_id := action_target_session_id_value; action_target_group_id := action_target_group_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InboundBusinessHeader.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InboundBusinessHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InboundBusinessHeader.eq_dec]. Defined.

  End OrderMassActionRequestMessage.

End B3DerivativesBinaryEntryPointV71.
