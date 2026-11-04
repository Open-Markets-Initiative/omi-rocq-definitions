From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Securities Industry Automation Corporation Output

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
      - a run counted by a field
      - the dispatch that chooses a message by its type
      - a field present only on a condition

    License: MIT No Attribution
  *)

Module SiacCqsOutputV191.

  Module SipBlockTimestamp.

    (** Sip Block Timestamp *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
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

  End SipBlockTimestamp.

  Module BlockHeader.

    (** Cta Output packet header *)
    Record t := {
      version : N;
      block_size : N;
      data_feed_indicator : list byte;
      retransmission_indicator : list byte;
      block_sequence_number : N;
      messages_in_block : N;
      sip_block_timestamp : SipBlockTimestamp.t;
      block_checksum : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 1)%N /\
      (block_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (data_feed_indicator record) = 1 /\
      Datatypes.length (retransmission_indicator record) = 1 /\
      (block_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (messages_in_block record < 256 ^ N.of_nat 1)%N /\
      SipBlockTimestamp.bounded (sip_block_timestamp record) /\
      (block_checksum record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record) ++
      encode_uint 2 (block_size record) ++
      encode_bytes 1 (data_feed_indicator record) ++
      encode_bytes 1 (retransmission_indicator record) ++
      encode_uint 4 (block_sequence_number record) ++
      encode_uint 1 (messages_in_block record) ++
      SipBlockTimestamp.encode (sip_block_timestamp record) ++
      encode_uint 2 (block_checksum record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (version_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (block_size_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (data_feed_indicator_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (retransmission_indicator_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (block_sequence_number_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (messages_in_block_value, bytes) =>
                              match SipBlockTimestamp.decode bytes with
                              | None => None
                              | Some (sip_block_timestamp_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (block_checksum_value, bytes) =>
                                      Some ({| version := version_value; block_size := block_size_value; data_feed_indicator := data_feed_indicator_value; retransmission_indicator := retransmission_indicator_value; block_sequence_number := block_sequence_number_value; messages_in_block := messages_in_block_value; sip_block_timestamp := sip_block_timestamp_value; block_checksum := block_checksum_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !SipBlockTimestamp.encode_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite SipBlockTimestamp.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SipBlockTimestamp.eq_dec]. Defined.

  End BlockHeader.

  Module ParticipantTimestamp.

    (** Participant Timestamp *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
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

  End ParticipantTimestamp.

  Module AdministrativeUnformattedMessage.

    (** The Administrative Unformatted (free form text) Category A message is designed to facilitate non-computerized miscellaneous information messages to CQS *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (text record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 4 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (text_value, bytes) =>
                              Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; text := text_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End AdministrativeUnformattedMessage.

  Module StartOfDayMessage.

    (** The Start of Day message signals the start of normal data dissemination over the multicast lines *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End StartOfDayMessage.

  Module FinraCloseMessage.

    (** The FINRA Close message is transmitted by FINRA to CQS to indicate the Close state of FINRA Market Maker(s). *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End FinraCloseMessage.

  Module ResetBlockSequenceNumberMessage.

    (** The Reset Block Sequence Number message is transmitted when the block sequence number on an output multicast line requires resetting. *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End ResetBlockSequenceNumberMessage.

  Module StartOfTestCycleMessage.

    (** The Start of Test Cycle message is transmitted to signal the beginning of the transmission of test message cycles *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End StartOfTestCycleMessage.

  Module EndOfTestCycleMessage.

    (** The End of Test Cycle message is transmitted to signal the end of the transmission of the repeated free form text test message cycles *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End EndOfTestCycleMessage.

  Module FinraOpenMessage.

    (** The FINRA Open message is transmitted by FINRA to CQS *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End FinraOpenMessage.

  Module DisasterRecoveryDataCenterActivationMessage.

    (** The Disaster Recovery Data Center Activation message is transmitted to signify that the Consolidated Quotation System (CQS) has switched processing from the Primary Data Center to the Disaster Recovery Data Center *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End DisasterRecoveryDataCenterActivationMessage.

  Module LineIntegrityMessage.

    (** The Line Integrity message is transmitted over the multicast lines at intervals of sixty (60) seconds to verify continued integrity of multicast transmission *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End LineIntegrityMessage.

  Module EndOfDayMessage.

    (** The End of Day message is transmitted over the multicast lines to advise all Data Recipients that there are no further messages of any type transmitted for the day *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End EndOfDayMessage.

  Module MarketWideCircuitBreakerDeclineLevelStatusMessage.

    (** The Market-Wide Circuit Breaker Decline Level Status message is used to report the calculated Level 1, Level 2 and Level 3 threshold values for the current trading day necessary to trigger a circuit breaker *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      mwcb_level_1 : N;
      mwcb_level_2 : N;
      mwcb_level_3 : N;
      reserved : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N /\
      (reserved record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_uint 8 (mwcb_level_1 record) ++
      encode_uint 8 (mwcb_level_2 record) ++
      encode_uint 8 (mwcb_level_3 record) ++
      encode_uint 1 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (mwcb_level_1_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (mwcb_level_2_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (mwcb_level_3_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (reserved_value, bytes) =>
                                          Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; mwcb_level_1 := mwcb_level_1_value; mwcb_level_2 := mwcb_level_2_value; mwcb_level_3 := mwcb_level_3_value; reserved := reserved_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End MarketWideCircuitBreakerDeclineLevelStatusMessage.

  Module MarketWideCircuitBreakerStatusMessage.

    (** The Market-Wide Circuit Breaker Status message is used to report the Market-Wide Circuit Breaker threshold Level that has been breached. *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      market_wide_circuit_breaker_level_indicator : list byte;
      reserved : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_wide_circuit_breaker_level_indicator record) = 1 /\
      (reserved record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 1 (market_wide_circuit_breaker_level_indicator record) ++
      encode_uint 1 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (market_wide_circuit_breaker_level_indicator_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reserved_value, bytes) =>
                                  Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; market_wide_circuit_breaker_level_indicator := market_wide_circuit_breaker_level_indicator_value; reserved := reserved_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End MarketWideCircuitBreakerStatusMessage.

  Module AuctionStatusMessage.

    (** The Auction Status message is used when a Participant in a Cta eligible security *)
    Record t := {
      participant_id : list byte;
      participant_timestamp : ParticipantTimestamp.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol_long : list byte;
      instrument_type : list byte;
      auction_collar_reference_price : N;
      auction_collar_upper_threshold_price : N;
      auction_collar_lower_threshold_price : N;
      number_of_extensions : N;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      future : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      ParticipantTimestamp.bounded (participant_timestamp record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol_long record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      (auction_collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_upper_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_lower_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (number_of_extensions record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (future record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      ParticipantTimestamp.encode (participant_timestamp record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol_long record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_uint 8 (auction_collar_reference_price record) ++
      encode_uint 8 (auction_collar_upper_threshold_price record) ++
      encode_uint 8 (auction_collar_lower_threshold_price record) ++
      encode_uint 1 (number_of_extensions record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 1 (future record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match ParticipantTimestamp.decode bytes with
          | None => None
          | Some (participant_timestamp_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (security_symbol_long_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (auction_collar_reference_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (auction_collar_upper_threshold_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (auction_collar_lower_threshold_price_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (number_of_extensions_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (short_sale_restriction_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (primary_listing_market_participant_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (financial_status_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (future_value, bytes) =>
                                                                  Some ({| participant_id := participant_id_value; participant_timestamp := participant_timestamp_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol_long := security_symbol_long_value; instrument_type := instrument_type_value; auction_collar_reference_price := auction_collar_reference_price_value; auction_collar_upper_threshold_price := auction_collar_upper_threshold_price_value; auction_collar_lower_threshold_price := auction_collar_lower_threshold_price_value; number_of_extensions := number_of_extensions_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; future := future_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !ParticipantTimestamp.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite ParticipantTimestamp.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ParticipantTimestamp.eq_dec]. Defined.

  End AuctionStatusMessage.

  Module AdfTimestamp.

    (** Adf Timestamp *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
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

  End AdfTimestamp.

End SiacCqsOutputV191.
