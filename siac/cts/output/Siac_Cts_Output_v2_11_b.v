From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The Securities Industry Automation Corporation 

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
  *)

Module SiacCtsOutputV211B.

  Module SIPBlockTimestamp.

    (** Cta packet timestamp *)
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

  End SIPBlockTimestamp.

  Module BlockHeader.

    (** Cta Output packet header *)
    Record t := {
      version : N;
      block_size : N;
      data_feed_indicator : list byte;
      retransmission_indicator : list byte;
      block_sequence_number : N;
      messages_in_block : N;
      s_i_p_block_timestamp : SIPBlockTimestamp.t;
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
      SIPBlockTimestamp.bounded (s_i_p_block_timestamp record) /\
      (block_checksum record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record) ++
      encode_uint 2 (block_size record) ++
      encode_bytes 1 (data_feed_indicator record) ++
      encode_bytes 1 (retransmission_indicator record) ++
      encode_uint 4 (block_sequence_number record) ++
      encode_uint 1 (messages_in_block record) ++
      SIPBlockTimestamp.encode (s_i_p_block_timestamp record) ++
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
                              match SIPBlockTimestamp.decode bytes with
                              | None => None
                              | Some (s_i_p_block_timestamp_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (block_checksum_value, bytes) =>
                                      Some ({| version := version_value; block_size := block_size_value; data_feed_indicator := data_feed_indicator_value; retransmission_indicator := retransmission_indicator_value; block_sequence_number := block_sequence_number_value; messages_in_block := messages_in_block_value; s_i_p_block_timestamp := s_i_p_block_timestamp_value; block_checksum := block_checksum_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !SIPBlockTimestamp.encode_length. reflexivity.
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
      rewrite SIPBlockTimestamp.decode_encode by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SIPBlockTimestamp.eq_dec]. Defined.

  End BlockHeader.

  Module Timestamp1.

    (** Timestamp 1 *)
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

  End Timestamp1.

  Module StartOfEndOfDaySummaryMessage.

    (** Used to signal the start of Consolidated End of Day Summary and Participant End of Day Summary message iterations *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp1.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End StartOfEndOfDaySummaryMessage.

  Module Timestamp12.

    (** Timestamp 1 *)
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

  End Timestamp12.

  Module EndOfEndOfDaySummaryMessage.

    (** Used to signal the end of Consolidated End of Day Summary and Participant End of Day Summary message iterations *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp12.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp12.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp12.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp12.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp12.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp12.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp12.eq_dec]. Defined.

  End EndOfEndOfDaySummaryMessage.

  Module Timestamp13.

    (** Timestamp 1 *)
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

  End Timestamp13.

  Module StartOfStartOfDaySummaryMessage.

    (** Used to signal the start of Start of Day Summary message iterations *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp13.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp13.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp13.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp13.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp13.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp13.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp13.eq_dec]. Defined.

  End StartOfStartOfDaySummaryMessage.

  Module Timestamp14.

    (** Timestamp 1 *)
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

  End Timestamp14.

  Module EndOfStartOfDaySummaryMessage.

    (** Used to signal the end of Start of Day Summary message iterations *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp14.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp14.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp14.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp14.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp14.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp14.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp14.eq_dec]. Defined.

  End EndOfStartOfDaySummaryMessage.

  Module Timestamp15.

    (** Timestamp 1 *)
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

  End Timestamp15.

  Module SymbolReferenceDataMessage.

    (** Symbol Reference Data message *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp15.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      prior_security_symbol : list byte;
      primary_listing_market_participant_id : list byte;
      primary_listing_market_previous_closing_price : N;
      consolidated_closing_price : N;
      round_lot_size : N;
      minimum_price_increment_indicator : list byte;
      luld_tier : list byte;
      luld_leverage_ratio : N;
      test : list byte;
      ipo : list byte;
      financial_status_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      halt_reason : list byte;
      instrument_type : list byte;
      reserved : list byte;
      second_reserved : list byte;
      reserved_128 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp15.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (prior_security_symbol record) = 11 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      (primary_listing_market_previous_closing_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_closing_price record < 256 ^ N.of_nat 8)%N /\
      (round_lot_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (minimum_price_increment_indicator record) = 1 /\
      Datatypes.length (luld_tier record) = 1 /\
      (luld_leverage_ratio record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (test record) = 1 /\
      Datatypes.length (ipo record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (halt_reason record) = 1 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (reserved record) = 1 /\
      Datatypes.length (second_reserved record) = 1 /\
      Datatypes.length (reserved_128 record) = 128.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp15.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 11 (prior_security_symbol record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_uint 8 (primary_listing_market_previous_closing_price record) ++
      encode_uint 8 (consolidated_closing_price record) ++
      encode_uint 2 (round_lot_size record) ++
      encode_bytes 1 (minimum_price_increment_indicator record) ++
      encode_bytes 1 (luld_tier record) ++
      encode_uint 4 (luld_leverage_ratio record) ++
      encode_bytes 1 (test record) ++
      encode_bytes 1 (ipo record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (halt_reason record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (reserved record) ++
      encode_bytes 1 (second_reserved record) ++
      encode_bytes 128 (reserved_128 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp15.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (prior_security_symbol_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (primary_listing_market_participant_id_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (primary_listing_market_previous_closing_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (consolidated_closing_price_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (round_lot_size_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (minimum_price_increment_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (luld_tier_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (luld_leverage_ratio_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (test_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (ipo_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (financial_status_indicator_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (halt_reason_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (instrument_type_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (reserved_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (second_reserved_value, bytes) =>
                                                                                              match decode_bytes 128 bytes with
                                                                                              | None => None
                                                                                              | Some (reserved_128_value, bytes) =>
                                                                                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; prior_security_symbol := prior_security_symbol_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; primary_listing_market_previous_closing_price := primary_listing_market_previous_closing_price_value; consolidated_closing_price := consolidated_closing_price_value; round_lot_size := round_lot_size_value; minimum_price_increment_indicator := minimum_price_increment_indicator_value; luld_tier := luld_tier_value; luld_leverage_ratio := luld_leverage_ratio_value; test := test_value; ipo := ipo_value; financial_status_indicator := financial_status_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; halt_reason := halt_reason_value; instrument_type := instrument_type_value; reserved := reserved_value; second_reserved := second_reserved_value; reserved_128 := reserved_128_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 205.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp15.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp15.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp15.eq_dec]. Defined.

  End SymbolReferenceDataMessage.

  Module Timestamp16.

    (** Timestamp 1 *)
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

  End Timestamp16.

  Module StartOfDayMessage.

    (** Signals the start of normal data dissemination over the multicast lines *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp16.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp16.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp16.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp16.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp16.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp16.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp16.eq_dec]. Defined.

  End StartOfDayMessage.

  Module Timestamp17.

    (** Timestamp 1 *)
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

  End Timestamp17.

  Module ResetBlockSequenceNumberMessage.

    (** Transmitted when the Block Sequence Number on an output multicast line requires resetting *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp17.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp17.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp17.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp17.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp17.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp17.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp17.eq_dec]. Defined.

  End ResetBlockSequenceNumberMessage.

  Module Timestamp18.

    (** Timestamp 1 *)
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

  End Timestamp18.

  Module DisasterRecoveryDataCenterActivationMessage.

    (** Signifies that the Consolidated Tape System has switched processing from the Primary Data Center to the Disaster Recovery Data Center *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp18.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp18.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp18.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp18.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp18.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp18.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp18.eq_dec]. Defined.

  End DisasterRecoveryDataCenterActivationMessage.

  Module Timestamp19.

    (** Timestamp 1 *)
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

  End Timestamp19.

  Module LineIntegrityMessage.

    (** Transmitted over the multicast lines at frequent intervals to verify continued integrity of multicast transmission *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp19.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp19.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp19.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp19.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp19.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp19.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp19.eq_dec]. Defined.

  End LineIntegrityMessage.

  Module Timestamp110.

    (** Timestamp 1 *)
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

  End Timestamp110.

  Module EndOfDayMessage.

    (** Transmitted over the multicast lines to advise all Data Recipients that there are no further messages to be transmitted for the day *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp110.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp110.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp110.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp110.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp110.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp110.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp110.eq_dec]. Defined.

  End EndOfDayMessage.

  Module Timestamp111.

    (** Timestamp 1 *)
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

  End Timestamp111.

  Module IndexMessage.

    (** The Index message contains the index and the index value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp111.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      index_symbol : list byte;
      index_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp111.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (index_symbol record) = 11 /\
      (index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp111.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (index_symbol record) ++
      encode_uint 8 (index_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp111.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (index_symbol_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (index_value_value, bytes) =>
                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; index_symbol := index_symbol_value; index_value := index_value_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp111.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp111.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp111.eq_dec]. Defined.

  End IndexMessage.

  Module Timestamp112.

    (** Timestamp 1 *)
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

  End Timestamp112.

  Module BidAndOfferIndexMessage.

    (** The Bid and Offer Index message contains the index Bid and Offer index values *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp112.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      index_symbol : list byte;
      bid_index_value : N;
      offer_index_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp112.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (index_symbol record) = 11 /\
      (bid_index_value record < 256 ^ N.of_nat 8)%N /\
      (offer_index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp112.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (index_symbol record) ++
      encode_uint 8 (bid_index_value record) ++
      encode_uint 8 (offer_index_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp112.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (index_symbol_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (bid_index_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (offer_index_value_value, bytes) =>
                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; index_symbol := index_symbol_value; bid_index_value := bid_index_value_value; offer_index_value := offer_index_value_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp112.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp112.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp112.eq_dec]. Defined.

  End BidAndOfferIndexMessage.

  Module Timestamp113.

    (** Timestamp 1 *)
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

  End Timestamp113.

  Module MarketWideCircuitBreakerDeclineLevelStatusMessage.

    (** Reports the calculated Level 1, Level 2 and Level 3 threshold values for the current trading day necessary to trigger a circuit breaker *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp113.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      mwcb_level_1 : N;
      mwcb_level_2 : N;
      mwcb_level_3 : N;
      reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp113.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp113.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_uint 8 (mwcb_level_1 record) ++
      encode_uint 8 (mwcb_level_2 record) ++
      encode_uint 8 (mwcb_level_3 record) ++
      encode_bytes 1 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp113.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (reserved_value, bytes) =>
                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; mwcb_level_1 := mwcb_level_1_value; mwcb_level_2 := mwcb_level_2_value; mwcb_level_3 := mwcb_level_3_value; reserved := reserved_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !Timestamp113.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp113.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp113.eq_dec]. Defined.

  End MarketWideCircuitBreakerDeclineLevelStatusMessage.

  Module Timestamp114.

    (** Timestamp 1 *)
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

  End Timestamp114.

  Module MarketWideCircuitBreakerStatusMessage.

    (** Reports the Market-Wide Circuit Breaker threshold Level that has been breached *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp114.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      market_wide_circuit_breaker_level_indicator : list byte;
      reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp114.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_wide_circuit_breaker_level_indicator record) = 1 /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp114.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 1 (market_wide_circuit_breaker_level_indicator record) ++
      encode_bytes 1 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp114.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (reserved_value, bytes) =>
                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; market_wide_circuit_breaker_level_indicator := market_wide_circuit_breaker_level_indicator_value; reserved := reserved_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !Timestamp114.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp114.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp114.eq_dec]. Defined.

  End MarketWideCircuitBreakerStatusMessage.

  Module Timestamp115.

    (** Timestamp 1 *)
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

  End Timestamp115.

  Module Timestamp116.

    (** Timestamp 1 *)
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

  End Timestamp116.

  Module Timestamp117.

    (** Timestamp 1 *)
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

  End Timestamp117.

  Module ApproximateTradesAndTotalDollarValueMessage.

    (** Allows a Participant to report the total trades and total dollar value of trades at their respective market centers *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp117.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      total_trades : N;
      dollar_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp117.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (total_trades record < 256 ^ N.of_nat 4)%N /\
      (dollar_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp117.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_uint 4 (total_trades record) ++
      encode_uint 8 (dollar_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp117.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (total_trades_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (dollar_value_value, bytes) =>
                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; total_trades := total_trades_value; dollar_value := dollar_value_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp117.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp117.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp117.eq_dec]. Defined.

  End ApproximateTradesAndTotalDollarValueMessage.

  Module Timestamp118.

    (** Timestamp 1 *)
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

  End Timestamp118.

  Module CrossingSessionSummaryMessage.

    (** Used to report the total volume and dollar value of trades transacted after the close of a Participant's regular session *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp118.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      crossing_session_i_total_trades_volume : N;
      crossing_session_ii_dollar_value : N;
      crossing_session_ii_total_trades_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp118.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_i_total_trades_volume record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_ii_dollar_value record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_ii_total_trades_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp118.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_uint 8 (crossing_session_i_total_trades_volume record) ++
      encode_uint 8 (crossing_session_ii_dollar_value record) ++
      encode_uint 8 (crossing_session_ii_total_trades_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp118.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (crossing_session_i_total_trades_volume_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (crossing_session_ii_dollar_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (crossing_session_ii_total_trades_volume_value, bytes) =>
                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; crossing_session_i_total_trades_volume := crossing_session_i_total_trades_volume_value; crossing_session_ii_dollar_value := crossing_session_ii_dollar_value_value; crossing_session_ii_total_trades_volume := crossing_session_ii_total_trades_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp118.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp118.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp118.eq_dec]. Defined.

  End CrossingSessionSummaryMessage.

  Module Timestamp119.

    (** Timestamp 1 *)
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

  End Timestamp119.

  Module CorrectedPriorDayTradeDateAndTime.

    (** The corrected prior day trade date and time *)
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

  End CorrectedPriorDayTradeDateAndTime.

  Module OriginalPriorDayTradeDateAndTime.

    (** The original prior day trade date and time *)
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

  End OriginalPriorDayTradeDateAndTime.

  Module PriorDayTradeCorrectionMessage.

    (** Used to correct a transaction originally reported on a trading day earlier than the current trading day. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp119.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      corrected_sale_condition : list byte;
      corrected_trade_price : N;
      corrected_trade_volume : N;
      corrected_sellers_sale_days : N;
      corrected_stop_stock_indicator : list byte;
      corrected_trade_through_exempt_indicator : list byte;
      corrected_short_sale_restriction_indicator : list byte;
      corrected_prior_day_trade_date_and_time : CorrectedPriorDayTradeDateAndTime.t;
      trade_reporting_facility_id : list byte;
      original_sale_condition : list byte;
      original_trade_price : N;
      original_trade_volume : N;
      original_sellers_sale_days : N;
      original_stop_stock_indicator : list byte;
      original_trade_through_exempt_indicator : list byte;
      original_short_sale_restriction_indicator : list byte;
      original_prior_day_trade_date_and_time : OriginalPriorDayTradeDateAndTime.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp119.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (corrected_sale_condition record) = 4 /\
      (corrected_trade_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_trade_volume record < 256 ^ N.of_nat 4)%N /\
      (corrected_sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (corrected_stop_stock_indicator record) = 1 /\
      Datatypes.length (corrected_trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (corrected_short_sale_restriction_indicator record) = 1 /\
      CorrectedPriorDayTradeDateAndTime.bounded (corrected_prior_day_trade_date_and_time record) /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      Datatypes.length (original_sale_condition record) = 4 /\
      (original_trade_price record < 256 ^ N.of_nat 8)%N /\
      (original_trade_volume record < 256 ^ N.of_nat 4)%N /\
      (original_sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (original_stop_stock_indicator record) = 1 /\
      Datatypes.length (original_trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (original_short_sale_restriction_indicator record) = 1 /\
      OriginalPriorDayTradeDateAndTime.bounded (original_prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp119.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 4 (corrected_sale_condition record) ++
      encode_uint 8 (corrected_trade_price record) ++
      encode_uint 4 (corrected_trade_volume record) ++
      encode_uint 1 (corrected_sellers_sale_days record) ++
      encode_bytes 1 (corrected_stop_stock_indicator record) ++
      encode_bytes 1 (corrected_trade_through_exempt_indicator record) ++
      encode_bytes 1 (corrected_short_sale_restriction_indicator record) ++
      CorrectedPriorDayTradeDateAndTime.encode (corrected_prior_day_trade_date_and_time record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      encode_bytes 4 (original_sale_condition record) ++
      encode_uint 8 (original_trade_price record) ++
      encode_uint 4 (original_trade_volume record) ++
      encode_uint 1 (original_sellers_sale_days record) ++
      encode_bytes 1 (original_stop_stock_indicator record) ++
      encode_bytes 1 (original_trade_through_exempt_indicator record) ++
      encode_bytes 1 (original_short_sale_restriction_indicator record) ++
      OriginalPriorDayTradeDateAndTime.encode (original_prior_day_trade_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp119.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (corrected_sale_condition_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (corrected_trade_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (corrected_trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (corrected_sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (corrected_stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (corrected_trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (corrected_short_sale_restriction_indicator_value, bytes) =>
                                                              match CorrectedPriorDayTradeDateAndTime.decode bytes with
                                                              | None => None
                                                              | Some (corrected_prior_day_trade_date_and_time_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trade_reporting_facility_id_value, bytes) =>
                                                                      match decode_bytes 4 bytes with
                                                                      | None => None
                                                                      | Some (original_sale_condition_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (original_trade_price_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (original_trade_volume_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (original_sellers_sale_days_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (original_stop_stock_indicator_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (original_trade_through_exempt_indicator_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (original_short_sale_restriction_indicator_value, bytes) =>
                                                                                                  match OriginalPriorDayTradeDateAndTime.decode bytes with
                                                                                                  | None => None
                                                                                                  | Some (original_prior_day_trade_date_and_time_value, bytes) =>
                                                                                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; corrected_sale_condition := corrected_sale_condition_value; corrected_trade_price := corrected_trade_price_value; corrected_trade_volume := corrected_trade_volume_value; corrected_sellers_sale_days := corrected_sellers_sale_days_value; corrected_stop_stock_indicator := corrected_stop_stock_indicator_value; corrected_trade_through_exempt_indicator := corrected_trade_through_exempt_indicator_value; corrected_short_sale_restriction_indicator := corrected_short_sale_restriction_indicator_value; corrected_prior_day_trade_date_and_time := corrected_prior_day_trade_date_and_time_value; trade_reporting_facility_id := trade_reporting_facility_id_value; original_sale_condition := original_sale_condition_value; original_trade_price := original_trade_price_value; original_trade_volume := original_trade_volume_value; original_sellers_sale_days := original_sellers_sale_days_value; original_stop_stock_indicator := original_stop_stock_indicator_value; original_trade_through_exempt_indicator := original_trade_through_exempt_indicator_value; original_short_sale_restriction_indicator := original_short_sale_restriction_indicator_value; original_prior_day_trade_date_and_time := original_prior_day_trade_date_and_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 91.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp119.encode_length, !encode_uint_length, !CorrectedPriorDayTradeDateAndTime.encode_length, !OriginalPriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 bound_23]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp119.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite CorrectedPriorDayTradeDateAndTime.decode_encode by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite OriginalPriorDayTradeDateAndTime.decode_encode by exact bound_23.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp119.eq_dec | apply CorrectedPriorDayTradeDateAndTime.eq_dec | apply OriginalPriorDayTradeDateAndTime.eq_dec]. Defined.

  End PriorDayTradeCorrectionMessage.

  Module Timestamp120.

    (** Timestamp 1 *)
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

  End Timestamp120.

  Module SaleCondition4.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition4.

  Module PriorDayTradeDateAndTime.

    (** The date and time the prior day trade was executed *)
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

  End PriorDayTradeDateAndTime.

  Module PriorDayTradeMessage.

    (** Used to report a CTA Equity, Local Issue or Bond transaction which occurred earlier than the current trading day and was not reported. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp120.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition4.t;
      trade_price : N;
      trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp120.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition4.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp120.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition4.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      PriorDayTradeDateAndTime.encode (prior_day_trade_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp120.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition4.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (trade_reporting_facility_id_value, bytes) =>
                                                                  match PriorDayTradeDateAndTime.decode bytes with
                                                                  | None => None
                                                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp120.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !PriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp120.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition4.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite PriorDayTradeDateAndTime.decode_encode by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp120.eq_dec | apply SaleCondition4.eq_dec | apply PriorDayTradeDateAndTime.eq_dec]. Defined.

  End PriorDayTradeMessage.

  Module Timestamp121.

    (** Timestamp 1 *)
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

  End Timestamp121.

  Module SaleCondition42.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition42.

  Module PriorDayTradeDateAndTime2.

    (** The date and time the prior day trade was executed *)
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

  End PriorDayTradeDateAndTime2.

  Module PriorDayTradeCancelErrorMessage.

    (** Used to report the cancellation of a trade or error a trade that never took place but was reported, for transactions originally reported earlier than the current day. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp121.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition42.t;
      trade_price : N;
      trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime2.t;
      cancel_error_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp121.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition42.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime2.bounded (prior_day_trade_date_and_time record) /\
      Datatypes.length (cancel_error_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp121.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition42.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      PriorDayTradeDateAndTime2.encode (prior_day_trade_date_and_time record) ++
      encode_bytes 1 (cancel_error_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp121.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition42.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (trade_reporting_facility_id_value, bytes) =>
                                                                  match PriorDayTradeDateAndTime2.decode bytes with
                                                                  | None => None
                                                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (cancel_error_action_value, bytes) =>
                                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value; cancel_error_action := cancel_error_action_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp121.encode_length, !encode_uint_length, !SaleCondition42.encode_length, !PriorDayTradeDateAndTime2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp121.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition42.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite PriorDayTradeDateAndTime2.decode_encode by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp121.eq_dec | apply SaleCondition42.eq_dec | apply PriorDayTradeDateAndTime2.eq_dec]. Defined.

  End PriorDayTradeCancelErrorMessage.

  Module Timestamp122.

    (** Timestamp 1 *)
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

  End Timestamp122.

  Module SaleCondition43.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition43.

  Module PriorDayTradeDateAndTime3.

    (** The date and time the prior day trade was executed *)
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

  End PriorDayTradeDateAndTime3.

  Module FractionalPriorDayTradeCorrectionMessage.

    (** Used to correct a transaction originally reported on a trading day earlier than the current trading day. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp122.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition43.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp122.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition43.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime3.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp122.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition43.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      PriorDayTradeDateAndTime3.encode (prior_day_trade_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp122.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition43.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (fractional_trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (trade_reporting_facility_id_value, bytes) =>
                                                                  match PriorDayTradeDateAndTime3.decode bytes with
                                                                  | None => None
                                                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; fractional_trade_volume := fractional_trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp122.encode_length, !encode_uint_length, !SaleCondition43.encode_length, !PriorDayTradeDateAndTime3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp122.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition43.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite PriorDayTradeDateAndTime3.decode_encode by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp122.eq_dec | apply SaleCondition43.eq_dec | apply PriorDayTradeDateAndTime3.eq_dec]. Defined.

  End FractionalPriorDayTradeCorrectionMessage.

  Module Timestamp123.

    (** Timestamp 1 *)
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

  End Timestamp123.

  Module SaleCondition44.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition44.

  Module PriorDayTradeDateAndTime4.

    (** The date and time the prior day trade was executed *)
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

  End PriorDayTradeDateAndTime4.

  Module FractionalPriorDayTradeMessage.

    (** Used to report a CTA Equity, Local Issue or Bond transaction which occurred earlier than the current trading day and was not reported. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp123.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition44.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime4.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp123.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition44.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime4.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp123.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition44.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      PriorDayTradeDateAndTime4.encode (prior_day_trade_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp123.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition44.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (fractional_trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (trade_reporting_facility_id_value, bytes) =>
                                                                  match PriorDayTradeDateAndTime4.decode bytes with
                                                                  | None => None
                                                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; fractional_trade_volume := fractional_trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp123.encode_length, !encode_uint_length, !SaleCondition44.encode_length, !PriorDayTradeDateAndTime4.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp123.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition44.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite PriorDayTradeDateAndTime4.decode_encode by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp123.eq_dec | apply SaleCondition44.eq_dec | apply PriorDayTradeDateAndTime4.eq_dec]. Defined.

  End FractionalPriorDayTradeMessage.

  Module Timestamp124.

    (** Timestamp 1 *)
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

  End Timestamp124.

  Module SaleCondition45.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition45.

  Module PriorDayTradeDateAndTime5.

    (** The date and time the prior day trade was executed *)
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

  End PriorDayTradeDateAndTime5.

  Module FractionalPriorDayTradeCancelErrorMessage.

    (** Used to report the cancellation of a trade or error a trade that never took place but was reported, for transactions originally reported earlier than the current day. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp124.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition45.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime5.t;
      cancel_error_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp124.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition45.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime5.bounded (prior_day_trade_date_and_time record) /\
      Datatypes.length (cancel_error_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp124.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition45.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      PriorDayTradeDateAndTime5.encode (prior_day_trade_date_and_time record) ++
      encode_bytes 1 (cancel_error_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp124.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition45.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (fractional_trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (trade_reporting_facility_id_value, bytes) =>
                                                                  match PriorDayTradeDateAndTime5.decode bytes with
                                                                  | None => None
                                                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (cancel_error_action_value, bytes) =>
                                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; fractional_trade_volume := fractional_trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value; cancel_error_action := cancel_error_action_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp124.encode_length, !encode_uint_length, !SaleCondition45.encode_length, !PriorDayTradeDateAndTime5.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp124.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition45.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite PriorDayTradeDateAndTime5.decode_encode by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp124.eq_dec | apply SaleCondition45.eq_dec | apply PriorDayTradeDateAndTime5.eq_dec]. Defined.

  End FractionalPriorDayTradeCancelErrorMessage.

  Module Timestamp125.

    (** Timestamp 1 *)
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

  End Timestamp125.

  Module ConsolidatedStartOfDaySummaryMessage.

    (** Provides, by security, consolidated previous close price and previous close price date information for CTA eligible Equity, Local Issues and Bonds *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp125.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      summary_participant_id : list byte;
      previous_close_price_date : N;
      previous_close_price : N;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      number_of_participants : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp125.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (summary_participant_id record) = 1 /\
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (previous_close_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (number_of_participants record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp125.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (summary_participant_id record) ++
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (previous_close_price record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 1 (number_of_participants record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp125.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (summary_participant_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (previous_close_price_date_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (previous_close_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (short_sale_restriction_indicator_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (primary_listing_market_participant_id_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (financial_status_indicator_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (number_of_participants_value, bytes) =>
                                                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; summary_participant_id := summary_participant_id_value; previous_close_price_date := previous_close_price_date_value; previous_close_price := previous_close_price_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; number_of_participants := number_of_participants_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp125.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp125.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp125.eq_dec]. Defined.

  End ConsolidatedStartOfDaySummaryMessage.

  Module Timestamp126.

    (** Timestamp 1 *)
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

  End Timestamp126.

  Module ParticipantStartOfDaySummaryMessage.

    (** Provides, by security, Participant previous close price and previous close price date information for CTA eligible Equity, Local Issues and Bonds *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp126.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      summary_participant_id : list byte;
      previous_close_price_date : N;
      previous_close_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp126.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (summary_participant_id record) = 1 /\
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (previous_close_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp126.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (summary_participant_id record) ++
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (previous_close_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp126.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (summary_participant_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (previous_close_price_date_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (previous_close_price_value, bytes) =>
                                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; summary_participant_id := summary_participant_id_value; previous_close_price_date := previous_close_price_date_value; previous_close_price := previous_close_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp126.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp126.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp126.eq_dec]. Defined.

  End ParticipantStartOfDaySummaryMessage.

  Module Timestamp127.

    (** Timestamp 1 *)
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

  End Timestamp127.

  Module ConsolidatedEndOfDaySummaryMessage.

    (** Provides by security, the Consolidated High, Low, Last and Volume for CTA eligible Equity, Local Issues and Bonds. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp127.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      last_participant_id : list byte;
      previous_close_price_date : N;
      last_price : N;
      high_price : N;
      low_price : N;
      total_volume : N;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      number_of_participants : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp127.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (last_participant_id record) = 1 /\
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (number_of_participants record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp127.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (total_volume record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 1 (number_of_participants record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp127.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (last_participant_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (previous_close_price_date_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (last_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (high_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (low_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (total_volume_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (primary_listing_market_participant_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (financial_status_indicator_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (number_of_participants_value, bytes) =>
                                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; last_participant_id := last_participant_id_value; previous_close_price_date := previous_close_price_date_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; total_volume := total_volume_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; number_of_participants := number_of_participants_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 75.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp127.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp127.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp127.eq_dec]. Defined.

  End ConsolidatedEndOfDaySummaryMessage.

  Module Timestamp128.

    (** Timestamp 1 *)
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

  End Timestamp128.

  Module FractionalConsolidatedEndOfDaySummaryMessage.

    (** Provides by security, the Consolidated High, Low, Last and Volume for CTA eligible Equity, Local Issues and Bonds. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp128.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      last_participant_id : list byte;
      previous_close_price_date : N;
      last_price : N;
      high_price : N;
      low_price : N;
      fractional_total_volume : N;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      number_of_participants : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp128.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (last_participant_id record) = 1 /\
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (number_of_participants record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp128.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (fractional_total_volume record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 1 (number_of_participants record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp128.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (last_participant_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (previous_close_price_date_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (last_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (high_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (low_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (fractional_total_volume_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (primary_listing_market_participant_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (financial_status_indicator_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (number_of_participants_value, bytes) =>
                                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; last_participant_id := last_participant_id_value; previous_close_price_date := previous_close_price_date_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; fractional_total_volume := fractional_total_volume_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; number_of_participants := number_of_participants_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 75.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp128.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp128.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp128.eq_dec]. Defined.

  End FractionalConsolidatedEndOfDaySummaryMessage.

  Module Timestamp129.

    (** Timestamp 1 *)
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

  End Timestamp129.

  Module ParticipantEndOfDaySummaryMessage.

    (** Provides by security, the Participant Open, High, Low, Last, Volume and Tick information for CTA eligible securities, Local Issues and Bonds. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp129.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      summary_participant_id : list byte;
      previous_close_price_date : N;
      last_price : N;
      high_price : N;
      low_price : N;
      open_price : N;
      total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp129.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (summary_participant_id record) = 1 /\
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp129.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (summary_participant_id record) ++
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 8 (total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp129.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (summary_participant_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (previous_close_price_date_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (last_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (high_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (low_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (open_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (total_volume_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (tick_value, bytes) =>
                                                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; summary_participant_id := summary_participant_id_value; previous_close_price_date := previous_close_price_date_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; open_price := open_price_value; total_volume := total_volume_value; tick := tick_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp129.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp129.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp129.eq_dec]. Defined.

  End ParticipantEndOfDaySummaryMessage.

  Module Timestamp130.

    (** Timestamp 1 *)
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

  End Timestamp130.

  Module FractionalParticipantEndOfDaySummaryMessage.

    (** Provides by security, the Participant Open, High, Low, Last, Volume and Tick information for CTA eligible securities, Local Issues and Bonds. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp130.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      summary_participant_id : list byte;
      previous_close_price_date : N;
      last_price : N;
      high_price : N;
      low_price : N;
      open_price : N;
      fractional_total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp130.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (summary_participant_id record) = 1 /\
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp130.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (summary_participant_id record) ++
      encode_uint 4 (previous_close_price_date record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 8 (fractional_total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp130.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (summary_participant_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (previous_close_price_date_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (last_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (high_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (low_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (open_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (fractional_total_volume_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (tick_value, bytes) =>
                                                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; summary_participant_id := summary_participant_id_value; previous_close_price_date := previous_close_price_date_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; open_price := open_price_value; fractional_total_volume := fractional_total_volume_value; tick := tick_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp130.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp130.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp130.eq_dec]. Defined.

  End FractionalParticipantEndOfDaySummaryMessage.

  Module Timestamp131.

    (** Timestamp 1 *)
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

  End Timestamp131.

  Module AuctionStatusMessage.

    (** Used when a Participant in a CTA eligible security, Local Issue or a Bond requires Auction Information *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp131.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      auction_collar_reference_price : N;
      auction_collar_upper_threshold_price : N;
      auction_collar_lower_threshold_price : N;
      number_of_extensions : N;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      reserved_62 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp131.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      (auction_collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_upper_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_lower_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (number_of_extensions record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (reserved_62 record) = 62.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp131.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_uint 8 (auction_collar_reference_price record) ++
      encode_uint 8 (auction_collar_upper_threshold_price record) ++
      encode_uint 8 (auction_collar_lower_threshold_price record) ++
      encode_uint 1 (number_of_extensions record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 62 (reserved_62 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp131.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
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
                                                              match decode_bytes 62 bytes with
                                                              | None => None
                                                              | Some (reserved_62_value, bytes) =>
                                                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; auction_collar_reference_price := auction_collar_reference_price_value; auction_collar_upper_threshold_price := auction_collar_upper_threshold_price_value; auction_collar_lower_threshold_price := auction_collar_lower_threshold_price_value; number_of_extensions := number_of_extensions_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; reserved_62 := reserved_62_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 124.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp131.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp131.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp131.eq_dec]. Defined.

  End AuctionStatusMessage.

  Module Timestamp132.

    (** Timestamp 1 *)
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

  End Timestamp132.

  Module Timestamp2.

    (** Timestamp 2 *)
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

  End Timestamp2.

  Module TradeCorrectionMessage.

    (** Used to correct CTA eligible Equity, Local Issue or Bond information. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp132.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      corrected_sale_condition : list byte;
      corrected_trade_price : N;
      corrected_trade_volume : N;
      corrected_sellers_sale_days : N;
      corrected_stop_stock_indicator : list byte;
      corrected_trade_through_exempt_indicator : list byte;
      corrected_short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      timestamp_2 : Timestamp2.t;
      original_participant_reference_number : N;
      original_sale_condition : list byte;
      original_trade_price : N;
      original_trade_volume : N;
      original_sellers_sale_days : N;
      original_stop_stock_indicator : list byte;
      original_trade_through_exempt_indicator : list byte;
      original_short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      consolidated_previous_close_price_date : N;
      consolidated_last_participant_id : list byte;
      consolidated_last_price : N;
      consolidated_high_price : N;
      consolidated_low_price : N;
      consolidated_total_volume : N;
      consolidated_tick : list byte;
      participant_previous_close_price_date : N;
      participant_last_price : N;
      participant_high_price : N;
      participant_low_price : N;
      participant_open_price : N;
      participant_total_volume : N;
      participant_tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp132.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (corrected_sale_condition record) = 4 /\
      (corrected_trade_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_trade_volume record < 256 ^ N.of_nat 4)%N /\
      (corrected_sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (corrected_stop_stock_indicator record) = 1 /\
      Datatypes.length (corrected_trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (corrected_short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      Timestamp2.bounded (timestamp_2 record) /\
      (original_participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (original_sale_condition record) = 4 /\
      (original_trade_price record < 256 ^ N.of_nat 8)%N /\
      (original_trade_volume record < 256 ^ N.of_nat 4)%N /\
      (original_sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (original_stop_stock_indicator record) = 1 /\
      Datatypes.length (original_trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (original_short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (consolidated_previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (consolidated_last_participant_id record) = 1 /\
      (consolidated_last_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_high_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_low_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_total_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (consolidated_tick record) = 1 /\
      (participant_previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (participant_last_price record < 256 ^ N.of_nat 8)%N /\
      (participant_high_price record < 256 ^ N.of_nat 8)%N /\
      (participant_low_price record < 256 ^ N.of_nat 8)%N /\
      (participant_open_price record < 256 ^ N.of_nat 8)%N /\
      (participant_total_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (participant_tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp132.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 4 (corrected_sale_condition record) ++
      encode_uint 8 (corrected_trade_price record) ++
      encode_uint 4 (corrected_trade_volume record) ++
      encode_uint 1 (corrected_sellers_sale_days record) ++
      encode_bytes 1 (corrected_stop_stock_indicator record) ++
      encode_bytes 1 (corrected_trade_through_exempt_indicator record) ++
      encode_bytes 1 (corrected_short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      Timestamp2.encode (timestamp_2 record) ++
      encode_uint 8 (original_participant_reference_number record) ++
      encode_bytes 4 (original_sale_condition record) ++
      encode_uint 8 (original_trade_price record) ++
      encode_uint 4 (original_trade_volume record) ++
      encode_uint 1 (original_sellers_sale_days record) ++
      encode_bytes 1 (original_stop_stock_indicator record) ++
      encode_bytes 1 (original_trade_through_exempt_indicator record) ++
      encode_bytes 1 (original_short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 4 (consolidated_previous_close_price_date record) ++
      encode_bytes 1 (consolidated_last_participant_id record) ++
      encode_uint 8 (consolidated_last_price record) ++
      encode_uint 8 (consolidated_high_price record) ++
      encode_uint 8 (consolidated_low_price record) ++
      encode_uint 4 (consolidated_total_volume record) ++
      encode_bytes 1 (consolidated_tick record) ++
      encode_uint 4 (participant_previous_close_price_date record) ++
      encode_uint 8 (participant_last_price record) ++
      encode_uint 8 (participant_high_price record) ++
      encode_uint 8 (participant_low_price record) ++
      encode_uint 8 (participant_open_price record) ++
      encode_uint 4 (participant_total_volume record) ++
      encode_bytes 1 (participant_tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp132.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (corrected_sale_condition_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (corrected_trade_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (corrected_trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (corrected_sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (corrected_stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (corrected_trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (corrected_short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (trade_reporting_facility_id_value, bytes) =>
                                                                  match Timestamp2.decode bytes with
                                                                  | None => None
                                                                  | Some (timestamp_2_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (original_participant_reference_number_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (original_sale_condition_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (original_trade_price_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (original_trade_volume_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (original_sellers_sale_days_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (original_stop_stock_indicator_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (original_trade_through_exempt_indicator_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (original_short_sale_restriction_indicator_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (primary_listing_market_participant_id_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (financial_status_indicator_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (consolidated_previous_close_price_date_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (consolidated_last_participant_id_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (consolidated_last_price_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (consolidated_high_price_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (consolidated_low_price_value, bytes) =>
                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (consolidated_total_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (consolidated_tick_value, bytes) =>
                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (participant_previous_close_price_date_value, bytes) =>
                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (participant_last_price_value, bytes) =>
                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (participant_high_price_value, bytes) =>
                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (participant_low_price_value, bytes) =>
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (participant_open_price_value, bytes) =>
                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (participant_total_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (participant_tick_value, bytes) =>
                                                                                                                                                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; corrected_sale_condition := corrected_sale_condition_value; corrected_trade_price := corrected_trade_price_value; corrected_trade_volume := corrected_trade_volume_value; corrected_sellers_sale_days := corrected_sellers_sale_days_value; corrected_stop_stock_indicator := corrected_stop_stock_indicator_value; corrected_trade_through_exempt_indicator := corrected_trade_through_exempt_indicator_value; corrected_short_sale_restriction_indicator := corrected_short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; timestamp_2 := timestamp_2_value; original_participant_reference_number := original_participant_reference_number_value; original_sale_condition := original_sale_condition_value; original_trade_price := original_trade_price_value; original_trade_volume := original_trade_volume_value; original_sellers_sale_days := original_sellers_sale_days_value; original_stop_stock_indicator := original_stop_stock_indicator_value; original_trade_through_exempt_indicator := original_trade_through_exempt_indicator_value; original_short_sale_restriction_indicator := original_short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; consolidated_previous_close_price_date := consolidated_previous_close_price_date_value; consolidated_last_participant_id := consolidated_last_participant_id_value; consolidated_last_price := consolidated_last_price_value; consolidated_high_price := consolidated_high_price_value; consolidated_low_price := consolidated_low_price_value; consolidated_total_volume := consolidated_total_volume_value; consolidated_tick := consolidated_tick_value; participant_previous_close_price_date := participant_previous_close_price_date_value; participant_last_price := participant_last_price_value; participant_high_price := participant_high_price_value; participant_low_price := participant_low_price_value; participant_open_price := participant_open_price_value; participant_total_volume := participant_total_volume_value; participant_tick := participant_tick_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 168.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp132.encode_length, !encode_uint_length, !Timestamp2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 bound_39]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp132.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite Timestamp2.decode_encode by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp132.eq_dec | apply Timestamp2.eq_dec]. Defined.

  End TradeCorrectionMessage.

  Module Timestamp133.

    (** Timestamp 1 *)
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

  End Timestamp133.

  Module SaleCondition46.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition46.

  Module Timestamp22.

    (** Timestamp 2 *)
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

  End Timestamp22.

  Module LongTradeMessage.

    (** Used to report trade information for CTA eligible Equity, Local Issue or Bonds. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp133.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition46.t;
      trade_price : N;
      trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      trade_reporting_facility_id : list byte;
      timestamp_2 : Timestamp22.t;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      held_trade_indicator : list byte;
      consolidated_high_low_last_indicator : list byte;
      participant_open_high_low_last_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp133.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition46.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      Timestamp22.bounded (timestamp_2 record) /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (held_trade_indicator record) = 1 /\
      Datatypes.length (consolidated_high_low_last_indicator record) = 1 /\
      Datatypes.length (participant_open_high_low_last_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp133.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition46.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      Timestamp22.encode (timestamp_2 record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 1 (held_trade_indicator record) ++
      encode_bytes 1 (consolidated_high_low_last_indicator record) ++
      encode_bytes 1 (participant_open_high_low_last_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp133.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition46.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_reporting_facility_id_value, bytes) =>
                                                              match Timestamp22.decode bytes with
                                                              | None => None
                                                              | Some (timestamp_2_value, bytes) =>
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
                                                                              | Some (held_trade_indicator_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (consolidated_high_low_last_indicator_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (participant_open_high_low_last_indicator_value, bytes) =>
                                                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; timestamp_2 := timestamp_2_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; held_trade_indicator := held_trade_indicator_value; consolidated_high_low_last_indicator := consolidated_high_low_last_indicator_value; participant_open_high_low_last_indicator := participant_open_high_low_last_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp133.encode_length, !encode_uint_length, !SaleCondition46.encode_length, !Timestamp22.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp133.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition46.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite Timestamp22.decode_encode by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp133.eq_dec | apply SaleCondition46.eq_dec | apply Timestamp22.eq_dec]. Defined.

  End LongTradeMessage.

  Module Timestamp134.

    (** Timestamp 1 *)
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

  End Timestamp134.

  Module ShortTradeMessage.

    (** Used to report trade information for CTA eligible Equity only. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp134.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol_5 : list byte;
      sale_condition_1 : list byte;
      sale_condition_category : list byte;
      trade_price_2 : N;
      trade_volume_2 : N;
      primary_listing_market_participant_id : list byte;
      consolidated_high_low_last_indicator : list byte;
      participant_open_high_low_last_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp134.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol_5 record) = 5 /\
      Datatypes.length (sale_condition_1 record) = 1 /\
      Datatypes.length (sale_condition_category record) = 1 /\
      (trade_price_2 record < 256 ^ N.of_nat 2)%N /\
      (trade_volume_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (consolidated_high_low_last_indicator record) = 1 /\
      Datatypes.length (participant_open_high_low_last_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp134.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 5 (security_symbol_5 record) ++
      encode_bytes 1 (sale_condition_1 record) ++
      encode_bytes 1 (sale_condition_category record) ++
      encode_uint 2 (trade_price_2 record) ++
      encode_uint 2 (trade_volume_2 record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (consolidated_high_low_last_indicator record) ++
      encode_bytes 1 (participant_open_high_low_last_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp134.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (security_symbol_5_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (sale_condition_1_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sale_condition_category_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (trade_price_2_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (trade_volume_2_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (primary_listing_market_participant_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (consolidated_high_low_last_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (participant_open_high_low_last_indicator_value, bytes) =>
                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol_5 := security_symbol_5_value; sale_condition_1 := sale_condition_1_value; sale_condition_category := sale_condition_category_value; trade_price_2 := trade_price_2_value; trade_volume_2 := trade_volume_2_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; consolidated_high_low_last_indicator := consolidated_high_low_last_indicator_value; participant_open_high_low_last_indicator := participant_open_high_low_last_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp134.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp134.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp134.eq_dec]. Defined.

  End ShortTradeMessage.

  Module Timestamp135.

    (** Timestamp 1 *)
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

  End Timestamp135.

  Module SaleCondition47.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition47.

  Module Timestamp23.

    (** Timestamp 2 *)
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

  End Timestamp23.

  Module TradeCancelErrorMessage.

    (** Used to cancel or error CTA eligible securities, Local Issues or Bond information. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp135.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition47.t;
      trade_price : N;
      trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      trade_reporting_facility_id : list byte;
      original_participant_reference_number : N;
      timestamp_2 : Timestamp23.t;
      cancel_error_action : list byte;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      consolidated_previous_close_price_date : N;
      consolidated_last_participant_id : list byte;
      consolidated_last_price : N;
      consolidated_high_price : N;
      consolidated_low_price : N;
      consolidated_total_volume : N;
      consolidated_tick : list byte;
      participant_previous_close_price_date : N;
      participant_last_price : N;
      participant_high_price : N;
      participant_low_price : N;
      participant_open_price : N;
      participant_total_volume : N;
      participant_tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp135.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition47.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      (original_participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Timestamp23.bounded (timestamp_2 record) /\
      Datatypes.length (cancel_error_action record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (consolidated_previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (consolidated_last_participant_id record) = 1 /\
      (consolidated_last_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_high_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_low_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_total_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (consolidated_tick record) = 1 /\
      (participant_previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (participant_last_price record < 256 ^ N.of_nat 8)%N /\
      (participant_high_price record < 256 ^ N.of_nat 8)%N /\
      (participant_low_price record < 256 ^ N.of_nat 8)%N /\
      (participant_open_price record < 256 ^ N.of_nat 8)%N /\
      (participant_total_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (participant_tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp135.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition47.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      encode_uint 8 (original_participant_reference_number record) ++
      Timestamp23.encode (timestamp_2 record) ++
      encode_bytes 1 (cancel_error_action record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 4 (consolidated_previous_close_price_date record) ++
      encode_bytes 1 (consolidated_last_participant_id record) ++
      encode_uint 8 (consolidated_last_price record) ++
      encode_uint 8 (consolidated_high_price record) ++
      encode_uint 8 (consolidated_low_price record) ++
      encode_uint 4 (consolidated_total_volume record) ++
      encode_bytes 1 (consolidated_tick record) ++
      encode_uint 4 (participant_previous_close_price_date record) ++
      encode_uint 8 (participant_last_price record) ++
      encode_uint 8 (participant_high_price record) ++
      encode_uint 8 (participant_low_price record) ++
      encode_uint 8 (participant_open_price record) ++
      encode_uint 4 (participant_total_volume record) ++
      encode_bytes 1 (participant_tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp135.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition47.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_reporting_facility_id_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (original_participant_reference_number_value, bytes) =>
                                                                  match Timestamp23.decode bytes with
                                                                  | None => None
                                                                  | Some (timestamp_2_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (cancel_error_action_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (primary_listing_market_participant_id_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (financial_status_indicator_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (consolidated_previous_close_price_date_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (consolidated_last_participant_id_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (consolidated_last_price_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (consolidated_high_price_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (consolidated_low_price_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (consolidated_total_volume_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (consolidated_tick_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (participant_previous_close_price_date_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (participant_last_price_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (participant_high_price_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (participant_low_price_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (participant_open_price_value, bytes) =>
                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (participant_total_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (participant_tick_value, bytes) =>
                                                                                                                                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; original_participant_reference_number := original_participant_reference_number_value; timestamp_2 := timestamp_2_value; cancel_error_action := cancel_error_action_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; consolidated_previous_close_price_date := consolidated_previous_close_price_date_value; consolidated_last_participant_id := consolidated_last_participant_id_value; consolidated_last_price := consolidated_last_price_value; consolidated_high_price := consolidated_high_price_value; consolidated_low_price := consolidated_low_price_value; consolidated_total_volume := consolidated_total_volume_value; consolidated_tick := consolidated_tick_value; participant_previous_close_price_date := participant_previous_close_price_date_value; participant_last_price := participant_last_price_value; participant_high_price := participant_high_price_value; participant_low_price := participant_low_price_value; participant_open_price := participant_open_price_value; participant_total_volume := participant_total_volume_value; participant_tick := participant_tick_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 149.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp135.encode_length, !encode_uint_length, !SaleCondition47.encode_length, !Timestamp23.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 bound_33]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp135.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition47.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite Timestamp23.decode_encode by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp135.eq_dec | apply SaleCondition47.eq_dec | apply Timestamp23.eq_dec]. Defined.

  End TradeCancelErrorMessage.

  Module Timestamp136.

    (** Timestamp 1 *)
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

  End Timestamp136.

  Module Timestamp24.

    (** Timestamp 2 *)
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

  End Timestamp24.

  Module FractionalTradeCorrectionMessage.

    (** Used to correct CTA eligible Equity, Local Issue or Bond information. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp136.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      corrected_sale_condition : list byte;
      corrected_trade_price : N;
      corrected_fractional_trade_volume : N;
      corrected_sellers_sale_days : N;
      corrected_stop_stock_indicator : list byte;
      corrected_trade_through_exempt_indicator : list byte;
      corrected_short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      timestamp_2 : Timestamp24.t;
      original_participant_reference_number : N;
      original_sale_condition : list byte;
      original_trade_price : N;
      original_fractional_trade_volume : N;
      original_sellers_sale_days : N;
      original_stop_stock_indicator : list byte;
      original_trade_through_exempt_indicator : list byte;
      original_short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      consolidated_previous_close_price_date : N;
      consolidated_last_participant_id : list byte;
      consolidated_last_price : N;
      consolidated_high_price : N;
      consolidated_low_price : N;
      consolidated_fractional_total_volume : N;
      consolidated_tick : list byte;
      participant_previous_close_price_date : N;
      participant_last_price : N;
      participant_high_price : N;
      participant_low_price : N;
      participant_open_price : N;
      participant_fractional_total_volume : N;
      participant_tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp136.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (corrected_sale_condition record) = 4 /\
      (corrected_trade_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (corrected_sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (corrected_stop_stock_indicator record) = 1 /\
      Datatypes.length (corrected_trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (corrected_short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      Timestamp24.bounded (timestamp_2 record) /\
      (original_participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (original_sale_condition record) = 4 /\
      (original_trade_price record < 256 ^ N.of_nat 8)%N /\
      (original_fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (original_sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (original_stop_stock_indicator record) = 1 /\
      Datatypes.length (original_trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (original_short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (consolidated_previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (consolidated_last_participant_id record) = 1 /\
      (consolidated_last_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_high_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_low_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (consolidated_tick record) = 1 /\
      (participant_previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (participant_last_price record < 256 ^ N.of_nat 8)%N /\
      (participant_high_price record < 256 ^ N.of_nat 8)%N /\
      (participant_low_price record < 256 ^ N.of_nat 8)%N /\
      (participant_open_price record < 256 ^ N.of_nat 8)%N /\
      (participant_fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (participant_tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp136.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 4 (corrected_sale_condition record) ++
      encode_uint 8 (corrected_trade_price record) ++
      encode_uint 8 (corrected_fractional_trade_volume record) ++
      encode_uint 1 (corrected_sellers_sale_days record) ++
      encode_bytes 1 (corrected_stop_stock_indicator record) ++
      encode_bytes 1 (corrected_trade_through_exempt_indicator record) ++
      encode_bytes 1 (corrected_short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      Timestamp24.encode (timestamp_2 record) ++
      encode_uint 8 (original_participant_reference_number record) ++
      encode_bytes 4 (original_sale_condition record) ++
      encode_uint 8 (original_trade_price record) ++
      encode_uint 8 (original_fractional_trade_volume record) ++
      encode_uint 1 (original_sellers_sale_days record) ++
      encode_bytes 1 (original_stop_stock_indicator record) ++
      encode_bytes 1 (original_trade_through_exempt_indicator record) ++
      encode_bytes 1 (original_short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 4 (consolidated_previous_close_price_date record) ++
      encode_bytes 1 (consolidated_last_participant_id record) ++
      encode_uint 8 (consolidated_last_price record) ++
      encode_uint 8 (consolidated_high_price record) ++
      encode_uint 8 (consolidated_low_price record) ++
      encode_uint 8 (consolidated_fractional_total_volume record) ++
      encode_bytes 1 (consolidated_tick record) ++
      encode_uint 4 (participant_previous_close_price_date record) ++
      encode_uint 8 (participant_last_price record) ++
      encode_uint 8 (participant_high_price record) ++
      encode_uint 8 (participant_low_price record) ++
      encode_uint 8 (participant_open_price record) ++
      encode_uint 8 (participant_fractional_total_volume record) ++
      encode_bytes 1 (participant_tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp136.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (corrected_sale_condition_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (corrected_trade_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (corrected_fractional_trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (corrected_sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (corrected_stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (corrected_trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (corrected_short_sale_restriction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (trade_reporting_facility_id_value, bytes) =>
                                                                  match Timestamp24.decode bytes with
                                                                  | None => None
                                                                  | Some (timestamp_2_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (original_participant_reference_number_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (original_sale_condition_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (original_trade_price_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (original_fractional_trade_volume_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (original_sellers_sale_days_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (original_stop_stock_indicator_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (original_trade_through_exempt_indicator_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (original_short_sale_restriction_indicator_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (primary_listing_market_participant_id_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (financial_status_indicator_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (consolidated_previous_close_price_date_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (consolidated_last_participant_id_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (consolidated_last_price_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (consolidated_high_price_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (consolidated_low_price_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (consolidated_fractional_total_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (consolidated_tick_value, bytes) =>
                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (participant_previous_close_price_date_value, bytes) =>
                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (participant_last_price_value, bytes) =>
                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (participant_high_price_value, bytes) =>
                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (participant_low_price_value, bytes) =>
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (participant_open_price_value, bytes) =>
                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (participant_fractional_total_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (participant_tick_value, bytes) =>
                                                                                                                                                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; corrected_sale_condition := corrected_sale_condition_value; corrected_trade_price := corrected_trade_price_value; corrected_fractional_trade_volume := corrected_fractional_trade_volume_value; corrected_sellers_sale_days := corrected_sellers_sale_days_value; corrected_stop_stock_indicator := corrected_stop_stock_indicator_value; corrected_trade_through_exempt_indicator := corrected_trade_through_exempt_indicator_value; corrected_short_sale_restriction_indicator := corrected_short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; timestamp_2 := timestamp_2_value; original_participant_reference_number := original_participant_reference_number_value; original_sale_condition := original_sale_condition_value; original_trade_price := original_trade_price_value; original_fractional_trade_volume := original_fractional_trade_volume_value; original_sellers_sale_days := original_sellers_sale_days_value; original_stop_stock_indicator := original_stop_stock_indicator_value; original_trade_through_exempt_indicator := original_trade_through_exempt_indicator_value; original_short_sale_restriction_indicator := original_short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; consolidated_previous_close_price_date := consolidated_previous_close_price_date_value; consolidated_last_participant_id := consolidated_last_participant_id_value; consolidated_last_price := consolidated_last_price_value; consolidated_high_price := consolidated_high_price_value; consolidated_low_price := consolidated_low_price_value; consolidated_fractional_total_volume := consolidated_fractional_total_volume_value; consolidated_tick := consolidated_tick_value; participant_previous_close_price_date := participant_previous_close_price_date_value; participant_last_price := participant_last_price_value; participant_high_price := participant_high_price_value; participant_low_price := participant_low_price_value; participant_open_price := participant_open_price_value; participant_fractional_total_volume := participant_fractional_total_volume_value; participant_tick := participant_tick_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 184.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp136.encode_length, !encode_uint_length, !Timestamp24.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 bound_39]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp136.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite Timestamp24.decode_encode by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp136.eq_dec | apply Timestamp24.eq_dec]. Defined.

  End FractionalTradeCorrectionMessage.

  Module Timestamp137.

    (** Timestamp 1 *)
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

  End Timestamp137.

  Module SaleCondition48.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition48.

  Module Timestamp25.

    (** Timestamp 2 *)
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

  End Timestamp25.

  Module FractionalLongTradeMessage.

    (** Used to report trade information for CTA eligible Equity, Local Issue or Bonds. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp137.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition48.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      trade_reporting_facility_id : list byte;
      timestamp_2 : Timestamp25.t;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      held_trade_indicator : list byte;
      consolidated_high_low_last_indicator : list byte;
      participant_open_high_low_last_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp137.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition48.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      Timestamp25.bounded (timestamp_2 record) /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (held_trade_indicator record) = 1 /\
      Datatypes.length (consolidated_high_low_last_indicator record) = 1 /\
      Datatypes.length (participant_open_high_low_last_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp137.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition48.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      Timestamp25.encode (timestamp_2 record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 1 (held_trade_indicator record) ++
      encode_bytes 1 (consolidated_high_low_last_indicator record) ++
      encode_bytes 1 (participant_open_high_low_last_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp137.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition48.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (fractional_trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_reporting_facility_id_value, bytes) =>
                                                              match Timestamp25.decode bytes with
                                                              | None => None
                                                              | Some (timestamp_2_value, bytes) =>
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
                                                                              | Some (held_trade_indicator_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (consolidated_high_low_last_indicator_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (participant_open_high_low_last_indicator_value, bytes) =>
                                                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; fractional_trade_volume := fractional_trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; timestamp_2 := timestamp_2_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; held_trade_indicator := held_trade_indicator_value; consolidated_high_low_last_indicator := consolidated_high_low_last_indicator_value; participant_open_high_low_last_indicator := participant_open_high_low_last_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp137.encode_length, !encode_uint_length, !SaleCondition48.encode_length, !Timestamp25.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp137.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition48.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite Timestamp25.decode_encode by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp137.eq_dec | apply SaleCondition48.eq_dec | apply Timestamp25.eq_dec]. Defined.

  End FractionalLongTradeMessage.

  Module Timestamp138.

    (** Timestamp 1 *)
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

  End Timestamp138.

  Module TradingStatusMessage.

    (** Transmitted when a Participant in a CTA eligible security, Local Issue or a Bond elects to notify CTS of a Trading Halt, a Trading Resume, a Price Indication or a Market Imbalance *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp138.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      last_price : N;
      high_indication_price_upper_limit_price_band : N;
      low_indication_price_lower_limit_price_band : N;
      buy_volume : N;
      sell_volume : N;
      security_status : list byte;
      halt_reason : list byte;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      limit_up_limit_down_luld_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp138.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_indication_price_upper_limit_price_band record < 256 ^ N.of_nat 8)%N /\
      (low_indication_price_lower_limit_price_band record < 256 ^ N.of_nat 8)%N /\
      (buy_volume record < 256 ^ N.of_nat 4)%N /\
      (sell_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_status record) = 1 /\
      Datatypes.length (halt_reason record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (limit_up_limit_down_luld_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp138.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_indication_price_upper_limit_price_band record) ++
      encode_uint 8 (low_indication_price_lower_limit_price_band record) ++
      encode_uint 4 (buy_volume record) ++
      encode_uint 4 (sell_volume record) ++
      encode_bytes 1 (security_status record) ++
      encode_bytes 1 (halt_reason record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 1 (limit_up_limit_down_luld_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp138.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (high_indication_price_upper_limit_price_band_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (low_indication_price_lower_limit_price_band_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (buy_volume_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (sell_volume_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (security_status_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (halt_reason_value, bytes) =>
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
                                                                          | Some (limit_up_limit_down_luld_indicator_value, bytes) =>
                                                                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; last_price := last_price_value; high_indication_price_upper_limit_price_band := high_indication_price_upper_limit_price_band_value; low_indication_price_lower_limit_price_band := low_indication_price_lower_limit_price_band_value; buy_volume := buy_volume_value; sell_volume := sell_volume_value; security_status := security_status_value; halt_reason := halt_reason_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; limit_up_limit_down_luld_indicator := limit_up_limit_down_luld_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp138.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp138.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp138.eq_dec]. Defined.

  End TradingStatusMessage.

  Module Timestamp139.

    (** Timestamp 1 *)
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

  End Timestamp139.

  Module FractionalShortTradeMessage.

    (** Used to report trade information for CTA eligible Equity only. Volume is represented as a fractional value. Not published by CTS currently, message type is reserved for future use *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp139.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol_5 : list byte;
      sale_condition_1 : list byte;
      sale_condition_category : list byte;
      trade_price_2 : N;
      fractional_trade_volume_4 : N;
      primary_listing_market_participant_id : list byte;
      consolidated_high_low_last_indicator : list byte;
      participant_open_high_low_last_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp139.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol_5 record) = 5 /\
      Datatypes.length (sale_condition_1 record) = 1 /\
      Datatypes.length (sale_condition_category record) = 1 /\
      (trade_price_2 record < 256 ^ N.of_nat 2)%N /\
      (fractional_trade_volume_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (consolidated_high_low_last_indicator record) = 1 /\
      Datatypes.length (participant_open_high_low_last_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp139.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 5 (security_symbol_5 record) ++
      encode_bytes 1 (sale_condition_1 record) ++
      encode_bytes 1 (sale_condition_category record) ++
      encode_uint 2 (trade_price_2 record) ++
      encode_uint 4 (fractional_trade_volume_4 record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (consolidated_high_low_last_indicator record) ++
      encode_bytes 1 (participant_open_high_low_last_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp139.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (message_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (transaction_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_reference_number_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (security_symbol_5_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (sale_condition_1_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sale_condition_category_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (trade_price_2_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (fractional_trade_volume_4_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (primary_listing_market_participant_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (consolidated_high_low_last_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (participant_open_high_low_last_indicator_value, bytes) =>
                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol_5 := security_symbol_5_value; sale_condition_1 := sale_condition_1_value; sale_condition_category := sale_condition_category_value; trade_price_2 := trade_price_2_value; fractional_trade_volume_4 := fractional_trade_volume_4_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; consolidated_high_low_last_indicator := consolidated_high_low_last_indicator_value; participant_open_high_low_last_indicator := participant_open_high_low_last_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp139.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp139.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp139.eq_dec]. Defined.

  End FractionalShortTradeMessage.

  Module Timestamp140.

    (** Timestamp 1 *)
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

  End Timestamp140.

  Module SaleCondition49.

    (** Sale Condition 4 *)
    Record t := {
      category_1 : list byte;
      category_2 : list byte;
      category_3 : list byte;
      category_4 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (category_1 record) = 1 /\
      Datatypes.length (category_2 record) = 1 /\
      Datatypes.length (category_3 record) = 1 /\
      Datatypes.length (category_4 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (category_1 record) ++
      encode_bytes 1 (category_2 record) ++
      encode_bytes 1 (category_3 record) ++
      encode_bytes 1 (category_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (category_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (category_2_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (category_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (category_4_value, bytes) =>
                      Some ({| category_1 := category_1_value; category_2 := category_2_value; category_3 := category_3_value; category_4 := category_4_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SaleCondition49.

  Module Timestamp26.

    (** Timestamp 2 *)
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

  End Timestamp26.

  Module FractionalTradeCancelErrorMessage.

    (** Used to cancel or error CTA eligible securities, Local Issues or Bond information. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp140.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition49.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      trade_reporting_facility_id : list byte;
      original_participant_reference_number : N;
      timestamp_2 : Timestamp26.t;
      cancel_error_action : list byte;
      short_sale_restriction_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      consolidated_previous_close_price_date : N;
      consolidated_last_participant_id : list byte;
      consolidated_last_price : N;
      consolidated_high_price : N;
      consolidated_low_price : N;
      consolidated_fractional_total_volume : N;
      consolidated_tick : list byte;
      participant_previous_close_price_date : N;
      participant_last_price : N;
      participant_high_price : N;
      participant_low_price : N;
      participant_open_price : N;
      participant_fractional_total_volume : N;
      participant_tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp140.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition49.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      (original_participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Timestamp26.bounded (timestamp_2 record) /\
      Datatypes.length (cancel_error_action record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (consolidated_previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (consolidated_last_participant_id record) = 1 /\
      (consolidated_last_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_high_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_low_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (consolidated_tick record) = 1 /\
      (participant_previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      (participant_last_price record < 256 ^ N.of_nat 8)%N /\
      (participant_high_price record < 256 ^ N.of_nat 8)%N /\
      (participant_low_price record < 256 ^ N.of_nat 8)%N /\
      (participant_open_price record < 256 ^ N.of_nat 8)%N /\
      (participant_fractional_total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (participant_tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp140.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition49.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      encode_uint 8 (original_participant_reference_number record) ++
      Timestamp26.encode (timestamp_2 record) ++
      encode_bytes 1 (cancel_error_action record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 4 (consolidated_previous_close_price_date record) ++
      encode_bytes 1 (consolidated_last_participant_id record) ++
      encode_uint 8 (consolidated_last_price record) ++
      encode_uint 8 (consolidated_high_price record) ++
      encode_uint 8 (consolidated_low_price record) ++
      encode_uint 8 (consolidated_fractional_total_volume record) ++
      encode_bytes 1 (consolidated_tick record) ++
      encode_uint 4 (participant_previous_close_price_date record) ++
      encode_uint 8 (participant_last_price record) ++
      encode_uint 8 (participant_high_price record) ++
      encode_uint 8 (participant_low_price record) ++
      encode_uint 8 (participant_open_price record) ++
      encode_uint 8 (participant_fractional_total_volume record) ++
      encode_bytes 1 (participant_tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp140.decode bytes with
          | None => None
          | Some (timestamp_1_value, bytes) =>
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
                          | Some (security_symbol_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_type_value, bytes) =>
                                  match SaleCondition49.decode bytes with
                                  | None => None
                                  | Some (sale_condition_4_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (fractional_trade_volume_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sellers_sale_days_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (stop_stock_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_through_exempt_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_reporting_facility_id_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (original_participant_reference_number_value, bytes) =>
                                                                  match Timestamp26.decode bytes with
                                                                  | None => None
                                                                  | Some (timestamp_2_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (cancel_error_action_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (short_sale_restriction_indicator_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (primary_listing_market_participant_id_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (financial_status_indicator_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (consolidated_previous_close_price_date_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (consolidated_last_participant_id_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (consolidated_last_price_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (consolidated_high_price_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (consolidated_low_price_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (consolidated_fractional_total_volume_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (consolidated_tick_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (participant_previous_close_price_date_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (participant_last_price_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (participant_high_price_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (participant_low_price_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (participant_open_price_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (participant_fractional_total_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (participant_tick_value, bytes) =>
                                                                                                                                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_condition_4 := sale_condition_4_value; trade_price := trade_price_value; fractional_trade_volume := fractional_trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; original_participant_reference_number := original_participant_reference_number_value; timestamp_2 := timestamp_2_value; cancel_error_action := cancel_error_action_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; consolidated_previous_close_price_date := consolidated_previous_close_price_date_value; consolidated_last_participant_id := consolidated_last_participant_id_value; consolidated_last_price := consolidated_last_price_value; consolidated_high_price := consolidated_high_price_value; consolidated_low_price := consolidated_low_price_value; consolidated_fractional_total_volume := consolidated_fractional_total_volume_value; consolidated_tick := consolidated_tick_value; participant_previous_close_price_date := participant_previous_close_price_date_value; participant_last_price := participant_last_price_value; participant_high_price := participant_high_price_value; participant_low_price := participant_low_price_value; participant_open_price := participant_open_price_value; participant_fractional_total_volume := participant_fractional_total_volume_value; participant_tick := participant_tick_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 161.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp140.encode_length, !encode_uint_length, !SaleCondition49.encode_length, !Timestamp26.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 bound_33]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp140.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleCondition49.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite Timestamp26.decode_encode by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp140.eq_dec | apply SaleCondition49.eq_dec | apply Timestamp26.eq_dec]. Defined.

  End FractionalTradeCancelErrorMessage.

End SiacCtsOutputV211B.
