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
  *)

Module SiacCtsOutputV191.

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

  Module StartOfEndOfDayMessage.

    (** The Start of End of Day message signals the start of Consolidated End of Day Summary and Participant End of Day Summary message iterations *)
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

  End StartOfEndOfDayMessage.

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

  Module EndOfEndOfDayMessage.

    (** The End of End of Day message signals the end of Consolidated End of Day Summary and Participant End of Day Summary message iterations *)
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

  End EndOfEndOfDayMessage.

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

  Module StartOfStartOfDayMessage.

    (** The Start of Start of Day message signals the end of Consolidated End of Day Summary and Participant End of Day Summary message iterations *)
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

  End StartOfStartOfDayMessage.

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

  Module EndOfStartOfDayMessage.

    (** The End of Start of Day message signals the start of Start of Day Summary message iterations *)
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

  End EndOfStartOfDayMessage.

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

  Module AdministrativeUnformattedMessage.

    (** The Administrative Unformatted (free form text) Category A message is designed to facilitate non-computerized miscellaneous information messages to CQS *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp15.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp15.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (text record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp15.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 4 (text record).

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
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (text_value, bytes) =>
                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; text := text_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp15.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp15.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp15.eq_dec]. Defined.

  End AdministrativeUnformattedMessage.

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

    (** The Start of Day message signals the start of normal data dissemination over the multicast lines *)
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

    (** The Reset Block Sequence Number message is transmitted when the block sequence number on an output multicast line requires resetting. *)
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

  Module StartOfTestCycleMessage.

    (** The Start of Test Cycle message is transmitted to signal the beginning of the transmission of test message cycles *)
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

  End StartOfTestCycleMessage.

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

  Module EndOfTestCycleMessage.

    (** The End of Test Cycle message is transmitted to signal the end of the transmission of the repeated free form text test message cycles *)
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

  End EndOfTestCycleMessage.

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

  Module DisasterRecoveryDataCenterActivationMessage.

    (** The Disaster Recovery Data Center Activation message is transmitted to signify that the Consolidated Quotation System (CQS) has switched processing from the Primary Data Center to the Disaster Recovery Data Center *)
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

  End DisasterRecoveryDataCenterActivationMessage.

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

  Module LineIntegrityMessage.

    (** The Line Integrity message is transmitted over the multicast lines at intervals of sixty (60) seconds to verify continued integrity of multicast transmission *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp111.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp111.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp111.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

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
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp111.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp111.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp111.eq_dec]. Defined.

  End LineIntegrityMessage.

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

  Module EndOfDayMessage.

    (** The End of Day message is transmitted over the multicast lines to advise all Data Recipients that there are no further messages of any type transmitted for the day *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp112.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp112.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp112.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

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
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp112.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp112.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp112.eq_dec]. Defined.

  End EndOfDayMessage.

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

  Module IndexMessage.

    (** The Index message contains the index and the index value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp113.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      index_symbol : list byte;
      index_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp113.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (index_symbol record) = 11 /\
      (index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp113.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (index_symbol record) ++
      encode_uint 8 (index_value record).

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
      rewrite !length_app, !encode_bytes_length, !Timestamp113.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp113.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp113.eq_dec]. Defined.

  End IndexMessage.

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

  Module BidAndOfferIndexMessage.

    (** The Bid and Offer Index message contains the index Bid and Offer index values *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp114.t;
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
      Timestamp114.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (index_symbol record) = 11 /\
      (bid_index_value record < 256 ^ N.of_nat 8)%N /\
      (offer_index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp114.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp114.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp114.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp114.eq_dec]. Defined.

  End BidAndOfferIndexMessage.

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

  Module MarketWideCircuitBreakerDeclineLevelStatusMessage.

    (** The Market-Wide Circuit Breaker Decline Level Status message is used to report the calculated Level 1, Level 2 and Level 3 threshold values for the current trading day necessary to trigger a circuit breaker *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp115.t;
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
      Timestamp115.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N /\
      (reserved record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp115.encode (timestamp_1 record) ++
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
          match Timestamp115.decode bytes with
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
                                      match decode_uint 1 bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp115.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp115.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp115.eq_dec]. Defined.

  End MarketWideCircuitBreakerDeclineLevelStatusMessage.

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

  Module MarketWideCircuitBreakerStatusMessage.

    (** The Market-Wide Circuit Breaker Status message is used to report the Market-Wide Circuit Breaker threshold Level that has been breached. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp116.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      market_wide_circuit_breaker_level_indicator : list byte;
      reserved : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp116.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_wide_circuit_breaker_level_indicator record) = 1 /\
      (reserved record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp116.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 1 (market_wide_circuit_breaker_level_indicator record) ++
      encode_uint 1 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match Timestamp116.decode bytes with
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
                              match decode_uint 1 bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp116.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp116.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp116.eq_dec]. Defined.

  End MarketWideCircuitBreakerStatusMessage.

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

  Module ApproximateTradesAndTotalDollarValueMessage.

    (** The Approximate Trades and Total Dollar Value message allows a Participant to report the total trades and total dollar value of trades at their respective market centers. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp118.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      total_trades : N;
      dollar_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp118.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (total_trades record < 256 ^ N.of_nat 4)%N /\
      (dollar_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp118.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_uint 4 (total_trades record) ++
      encode_uint 8 (dollar_value record).

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
      rewrite !length_app, !encode_bytes_length, !Timestamp118.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp118.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp118.eq_dec]. Defined.

  End ApproximateTradesAndTotalDollarValueMessage.

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

  Module CrossingSessionSummaryMessage.

    (** The Crossing Session message is used to report the total volume and dollar value of trades transacted after the close of a Participant’s regular session. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp119.t;
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
      Timestamp119.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_i_total_trades_volume record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_ii_dollar_value record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_ii_total_trades_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp119.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp119.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp119.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp119.eq_dec]. Defined.

  End CrossingSessionSummaryMessage.

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

  Module SaleConditions.

    (** Sale Conditions *)
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

  End SaleConditions.

  Module PriorDayTradeDateAndTime.

    (** Prior Day Trade Date and Time *)
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

  Module CorrectedTrade.

    (** Corrected Trade *)
    Record t := {
      sale_conditions : SaleConditions.t;
      trade_price_long : N;
      trade_volume_long : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SaleConditions.bounded (sale_conditions record) /\
      (trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (trade_volume_long record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      PriorDayTradeDateAndTime.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      SaleConditions.encode (sale_conditions record) ++
      encode_uint 8 (trade_price_long record) ++
      encode_uint 4 (trade_volume_long record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      PriorDayTradeDateAndTime.encode (prior_day_trade_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SaleConditions.decode bytes with
      | None => None
      | Some (sale_conditions_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_price_long_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_volume_long_value, bytes) =>
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
                                  match PriorDayTradeDateAndTime.decode bytes with
                                  | None => None
                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                      Some ({| sale_conditions := sale_conditions_value; trade_price_long := trade_price_long_value; trade_volume_long := trade_volume_long_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value |}, bytes)
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
      rewrite !length_app, !SaleConditions.encode_length, !encode_uint_length, !encode_bytes_length, !PriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SaleConditions.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite PriorDayTradeDateAndTime.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditions.eq_dec | apply PriorDayTradeDateAndTime.eq_dec]. Defined.

  End CorrectedTrade.

  Module SaleConditions2.

    (** Sale Conditions *)
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

  End SaleConditions2.

  Module PriorDayTradeDateAndTime2.

    (** Prior Day Trade Date and Time *)
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

  Module OriginalTrade.

    (** Original Trade *)
    Record t := {
      sale_conditions : SaleConditions2.t;
      trade_price_long : N;
      trade_volume_long : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SaleConditions2.bounded (sale_conditions record) /\
      (trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (trade_volume_long record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      PriorDayTradeDateAndTime2.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      SaleConditions2.encode (sale_conditions record) ++
      encode_uint 8 (trade_price_long record) ++
      encode_uint 4 (trade_volume_long record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      PriorDayTradeDateAndTime2.encode (prior_day_trade_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SaleConditions2.decode bytes with
      | None => None
      | Some (sale_conditions_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_price_long_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_volume_long_value, bytes) =>
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
                                  match PriorDayTradeDateAndTime2.decode bytes with
                                  | None => None
                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                      Some ({| sale_conditions := sale_conditions_value; trade_price_long := trade_price_long_value; trade_volume_long := trade_volume_long_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value |}, bytes)
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
      rewrite !length_app, !SaleConditions2.encode_length, !encode_uint_length, !encode_bytes_length, !PriorDayTradeDateAndTime2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SaleConditions2.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite PriorDayTradeDateAndTime2.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditions2.eq_dec | apply PriorDayTradeDateAndTime2.eq_dec]. Defined.

  End OriginalTrade.

  Module PriorDayTradeCorrectionMessage.

    (** The Prior Day Correction message is used to correct a transaction originally reported on a trading day earlier than the current trading day *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp120.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      corrected_trade : CorrectedTrade.t;
      trade_reporting_facility_id : list byte;
      original_trade : OriginalTrade.t;
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
      CorrectedTrade.bounded (corrected_trade record) /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      OriginalTrade.bounded (original_trade record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp120.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      CorrectedTrade.encode (corrected_trade record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      OriginalTrade.encode (original_trade record).

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
                                  match CorrectedTrade.decode bytes with
                                  | None => None
                                  | Some (corrected_trade_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_reporting_facility_id_value, bytes) =>
                                          match OriginalTrade.decode bytes with
                                          | None => None
                                          | Some (original_trade_value, bytes) =>
                                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; corrected_trade := corrected_trade_value; trade_reporting_facility_id := trade_reporting_facility_id_value; original_trade := original_trade_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !Timestamp120.encode_length, !encode_uint_length, !CorrectedTrade.encode_length, !OriginalTrade.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp120.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite CorrectedTrade.decode_encode by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite OriginalTrade.decode_encode by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp120.eq_dec | apply CorrectedTrade.eq_dec | apply OriginalTrade.eq_dec]. Defined.

  End PriorDayTradeCorrectionMessage.

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

  Module SaleConditions3.

    (** Sale Conditions *)
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

  End SaleConditions3.

  Module PriorDayTradeDateAndTime3.

    (** Prior Day Trade Date and Time *)
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

  Module PriorDayTradeMessage.

    (** The Prior Day Trade message is used to report a Cta Equity, Local Issue or Bond transaction which occurred earlier than the current trading day and was not reported. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp121.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_conditions : SaleConditions3.t;
      trade_price : N;
      trade_volume : N;
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
      Timestamp121.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleConditions3.bounded (sale_conditions record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime3.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp121.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleConditions3.encode (sale_conditions record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
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
                                  match SaleConditions3.decode bytes with
                                  | None => None
                                  | Some (sale_conditions_value, bytes) =>
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
                                                                  match PriorDayTradeDateAndTime3.decode bytes with
                                                                  | None => None
                                                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_conditions := sale_conditions_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !Timestamp121.encode_length, !encode_uint_length, !SaleConditions3.encode_length, !PriorDayTradeDateAndTime3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp121.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleConditions3.decode_encode by exact bound_7.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp121.eq_dec | apply SaleConditions3.eq_dec | apply PriorDayTradeDateAndTime3.eq_dec]. Defined.

  End PriorDayTradeMessage.

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

  Module SaleConditions4.

    (** Sale Conditions *)
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

  End SaleConditions4.

  Module PriorDayTradeDateAndTime4.

    (** Prior Day Trade Date and Time *)
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

  Module PriorDayTradeCancelErrorMessage.

    (** The Prior Day Trade message is used to report a Cta Equity, Local Issue or Bond transaction which occurred earlier than the current trading day and was not reported. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp122.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_conditions : SaleConditions4.t;
      trade_price : N;
      trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime4.t;
      cancel_error_action : list byte;
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
      SaleConditions4.bounded (sale_conditions record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime4.bounded (prior_day_trade_date_and_time record) /\
      Datatypes.length (cancel_error_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp122.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleConditions4.encode (sale_conditions record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      PriorDayTradeDateAndTime4.encode (prior_day_trade_date_and_time record) ++
      encode_bytes 1 (cancel_error_action record).

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
                                  match SaleConditions4.decode bytes with
                                  | None => None
                                  | Some (sale_conditions_value, bytes) =>
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
                                                                  match PriorDayTradeDateAndTime4.decode bytes with
                                                                  | None => None
                                                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (cancel_error_action_value, bytes) =>
                                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_conditions := sale_conditions_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value; cancel_error_action := cancel_error_action_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !Timestamp122.encode_length, !encode_uint_length, !SaleConditions4.encode_length, !PriorDayTradeDateAndTime4.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp122.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleConditions4.decode_encode by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite PriorDayTradeDateAndTime4.decode_encode by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp122.eq_dec | apply SaleConditions4.eq_dec | apply PriorDayTradeDateAndTime4.eq_dec]. Defined.

  End PriorDayTradeCancelErrorMessage.

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

  Module ConsolidatedStartOfDaySummaryMessage.

    (** The Consolidated Start of Day Summary messages are transmitted shortly after the Multicast Line ‘Start of Day’ message *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp123.t;
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
      Timestamp123.bounded (timestamp_1 record) /\
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
      Timestamp123.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp123.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp123.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp123.eq_dec]. Defined.

  End ConsolidatedStartOfDaySummaryMessage.

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

  Module ParticipantStartOfDaySummaryMessage.

    (** The Participant Start of Day Summary messages are transmitted shortly after the Multicast Line ‘Start of Day’ message *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp124.t;
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
      Timestamp124.bounded (timestamp_1 record) /\
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
      Timestamp124.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp124.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp124.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp124.eq_dec]. Defined.

  End ParticipantStartOfDaySummaryMessage.

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

  Module ConsolidatedEndOfDaySummaryMessage.

    (** The Consolidated End of Day Summary messages are transmitted shortly before the "Goodnight" messages *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp125.t;
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
      Timestamp125.bounded (timestamp_1 record) /\
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
      Timestamp125.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp125.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp125.eq_dec]. Defined.

  End ConsolidatedEndOfDaySummaryMessage.

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

  Module ParticipantEndOfDaySummaryMessage.

    (** The Participant End of Day Summary messages are transmitted shortly before the ‘Goodnight’ messages. *)
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
      Timestamp126.bounded (timestamp_1 record) /\
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
      Timestamp126.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp126.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp126.eq_dec]. Defined.

  End ParticipantEndOfDaySummaryMessage.

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

  Module AuctionStatusMessage.

    (** The Auction Status message is used when a Participant in a Cta eligible security, Local Issue or a Bond requires Auction Information *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp127.t;
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
      future_use : list byte;
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
      (auction_collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_upper_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_lower_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (number_of_extensions record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (future_use record) = 62.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp127.encode (timestamp_1 record) ++
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
      encode_bytes 62 (future_use record).

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
                                                              | Some (future_use_value, bytes) =>
                                                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; auction_collar_reference_price := auction_collar_reference_price_value; auction_collar_upper_threshold_price := auction_collar_upper_threshold_price_value; auction_collar_lower_threshold_price := auction_collar_lower_threshold_price_value; number_of_extensions := number_of_extensions_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; future_use := future_use_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !Timestamp127.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp127.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp127.eq_dec]. Defined.

  End AuctionStatusMessage.

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

  Module SaleConditions5.

    (** Sale Conditions *)
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

  End SaleConditions5.

  Module PriorDayTradeDateAndTime5.

    (** Prior Day Trade Date and Time *)
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

  Module CorrectedTrade2.

    (** Corrected Trade *)
    Record t := {
      sale_conditions : SaleConditions5.t;
      trade_price_long : N;
      trade_volume_long : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime5.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SaleConditions5.bounded (sale_conditions record) /\
      (trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (trade_volume_long record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      PriorDayTradeDateAndTime5.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      SaleConditions5.encode (sale_conditions record) ++
      encode_uint 8 (trade_price_long record) ++
      encode_uint 4 (trade_volume_long record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      PriorDayTradeDateAndTime5.encode (prior_day_trade_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SaleConditions5.decode bytes with
      | None => None
      | Some (sale_conditions_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_price_long_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_volume_long_value, bytes) =>
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
                                  match PriorDayTradeDateAndTime5.decode bytes with
                                  | None => None
                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                      Some ({| sale_conditions := sale_conditions_value; trade_price_long := trade_price_long_value; trade_volume_long := trade_volume_long_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value |}, bytes)
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
      rewrite !length_app, !SaleConditions5.encode_length, !encode_uint_length, !encode_bytes_length, !PriorDayTradeDateAndTime5.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SaleConditions5.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite PriorDayTradeDateAndTime5.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditions5.eq_dec | apply PriorDayTradeDateAndTime5.eq_dec]. Defined.

  End CorrectedTrade2.

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

  Module SaleConditions6.

    (** Sale Conditions *)
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

  End SaleConditions6.

  Module PriorDayTradeDateAndTime6.

    (** Prior Day Trade Date and Time *)
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

  End PriorDayTradeDateAndTime6.

  Module OriginalTrade2.

    (** Original Trade *)
    Record t := {
      sale_conditions : SaleConditions6.t;
      trade_price_long : N;
      trade_volume_long : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime6.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SaleConditions6.bounded (sale_conditions record) /\
      (trade_price_long record < 256 ^ N.of_nat 8)%N /\
      (trade_volume_long record < 256 ^ N.of_nat 4)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      PriorDayTradeDateAndTime6.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      SaleConditions6.encode (sale_conditions record) ++
      encode_uint 8 (trade_price_long record) ++
      encode_uint 4 (trade_volume_long record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      PriorDayTradeDateAndTime6.encode (prior_day_trade_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SaleConditions6.decode bytes with
      | None => None
      | Some (sale_conditions_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_price_long_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_volume_long_value, bytes) =>
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
                                  match PriorDayTradeDateAndTime6.decode bytes with
                                  | None => None
                                  | Some (prior_day_trade_date_and_time_value, bytes) =>
                                      Some ({| sale_conditions := sale_conditions_value; trade_price_long := trade_price_long_value; trade_volume_long := trade_volume_long_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; prior_day_trade_date_and_time := prior_day_trade_date_and_time_value |}, bytes)
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
      rewrite !length_app, !SaleConditions6.encode_length, !encode_uint_length, !encode_bytes_length, !PriorDayTradeDateAndTime6.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SaleConditions6.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite PriorDayTradeDateAndTime6.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SaleConditions6.eq_dec | apply PriorDayTradeDateAndTime6.eq_dec]. Defined.

  End OriginalTrade2.

  Module ConsolidatedData.

    (** Consolidated Data *)
    Record t := {
      previous_close_price_date : N;
      last_participant_id : list byte;
      last_price : N;
      high_price : N;
      low_price : N;
      total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_participant_id record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_participant_id_value, bytes) =>
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
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_participant_id := last_participant_id_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; total_volume := total_volume_value; tick := tick_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConsolidatedData.

  Module ParticipantData.

    (** Participant Data *)
    Record t := {
      previous_close_price_date : N;
      last_participant_id : list byte;
      last_price : N;
      high_price : N;
      low_price : N;
      total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_participant_id record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_participant_id_value, bytes) =>
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
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_participant_id := last_participant_id_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; total_volume := total_volume_value; tick := tick_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParticipantData.

  Module TradeCorrectionMessage.

    (** The Trade Correction message is used to correct Cta eligible Equity, Local Issue or Bond information. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp128.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      corrected_trade : CorrectedTrade2.t;
      trade_reporting_facility_id : list byte;
      timestamp_2 : Timestamp2.t;
      original_participant_reference_number : N;
      original_trade : OriginalTrade2.t;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      consolidated_data : ConsolidatedData.t;
      participant_data : ParticipantData.t;
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
      CorrectedTrade2.bounded (corrected_trade record) /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      Timestamp2.bounded (timestamp_2 record) /\
      (original_participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      OriginalTrade2.bounded (original_trade record) /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      ConsolidatedData.bounded (consolidated_data record) /\
      ParticipantData.bounded (participant_data record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp128.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      CorrectedTrade2.encode (corrected_trade record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      Timestamp2.encode (timestamp_2 record) ++
      encode_uint 8 (original_participant_reference_number record) ++
      OriginalTrade2.encode (original_trade record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      ConsolidatedData.encode (consolidated_data record) ++
      ParticipantData.encode (participant_data record).

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
                                  match CorrectedTrade2.decode bytes with
                                  | None => None
                                  | Some (corrected_trade_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_reporting_facility_id_value, bytes) =>
                                          match Timestamp2.decode bytes with
                                          | None => None
                                          | Some (timestamp_2_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (original_participant_reference_number_value, bytes) =>
                                                  match OriginalTrade2.decode bytes with
                                                  | None => None
                                                  | Some (original_trade_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (primary_listing_market_participant_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (financial_status_indicator_value, bytes) =>
                                                              match ConsolidatedData.decode bytes with
                                                              | None => None
                                                              | Some (consolidated_data_value, bytes) =>
                                                                  match ParticipantData.decode bytes with
                                                                  | None => None
                                                                  | Some (participant_data_value, bytes) =>
                                                                      Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; corrected_trade := corrected_trade_value; trade_reporting_facility_id := trade_reporting_facility_id_value; timestamp_2 := timestamp_2_value; original_participant_reference_number := original_participant_reference_number_value; original_trade := original_trade_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; consolidated_data := consolidated_data_value; participant_data := participant_data_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 185.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp128.encode_length, !encode_uint_length, !CorrectedTrade2.encode_length, !Timestamp2.encode_length, !OriginalTrade2.encode_length, !ConsolidatedData.encode_length, !ParticipantData.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp128.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite CorrectedTrade2.decode_encode by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite Timestamp2.decode_encode by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite OriginalTrade2.decode_encode by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite ConsolidatedData.decode_encode by exact bound_14.
      rewrite ParticipantData.decode_encode by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp128.eq_dec | apply CorrectedTrade2.eq_dec | apply Timestamp2.eq_dec | apply OriginalTrade2.eq_dec | apply ConsolidatedData.eq_dec | apply ParticipantData.eq_dec]. Defined.

  End TradeCorrectionMessage.

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

  Module SaleConditions7.

    (** Sale Conditions *)
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

  End SaleConditions7.

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

    (** The Long Trade message is used to report trade information for Cta eligible Equity, Local Issue or Bonds. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp129.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_conditions : SaleConditions7.t;
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
      Timestamp129.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleConditions7.bounded (sale_conditions record) /\
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
      Timestamp129.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleConditions7.encode (sale_conditions record) ++
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
                                  match SaleConditions7.decode bytes with
                                  | None => None
                                  | Some (sale_conditions_value, bytes) =>
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
                                                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_conditions := sale_conditions_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; timestamp_2 := timestamp_2_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; held_trade_indicator := held_trade_indicator_value; consolidated_high_low_last_indicator := consolidated_high_low_last_indicator_value; participant_open_high_low_last_indicator := participant_open_high_low_last_indicator_value |}, bytes)
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !Timestamp129.encode_length, !encode_uint_length, !SaleConditions7.encode_length, !Timestamp22.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp129.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleConditions7.decode_encode by exact bound_7.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp129.eq_dec | apply SaleConditions7.eq_dec | apply Timestamp22.eq_dec]. Defined.

  End LongTradeMessage.

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

  Module TradingStatusMessage.

    (** The Trading Status message is transmitted when a Participant in a Cta eligible security, Local Issue or a Bond elects to notify CTS of an Opening Delay, a Trading Halt, a Trading Resume, a Price Indication or a Market Imbalance. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp130.t;
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
      limit_up_limit_down_indicator : list byte;
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
      Datatypes.length (limit_up_limit_down_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp130.encode (timestamp_1 record) ++
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
      encode_bytes 1 (limit_up_limit_down_indicator record).

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
                                                                          | Some (limit_up_limit_down_indicator_value, bytes) =>
                                                                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; last_price := last_price_value; high_indication_price_upper_limit_price_band := high_indication_price_upper_limit_price_band_value; low_indication_price_lower_limit_price_band := low_indication_price_lower_limit_price_band_value; buy_volume := buy_volume_value; sell_volume := sell_volume_value; security_status := security_status_value; halt_reason := halt_reason_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; limit_up_limit_down_indicator := limit_up_limit_down_indicator_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !Timestamp130.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp130.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp130.eq_dec]. Defined.

  End TradingStatusMessage.

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

  Module ShortTradeMessage.

    (** The Short Trade message is used to report trade information for Cta eligible Equity only (not used for Local Issues or Bonds) if the trade meets message format requirements otherwise Long Trade message is used. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp131.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol_short : list byte;
      sale_condition : list byte;
      sale_condition_category : list byte;
      trade_price_short : N;
      trade_volume_short : N;
      primary_listing_market_participant_id : list byte;
      consolidated_high_low_last_indicator : list byte;
      participant_open_high_low_last_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp131.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol_short record) = 5 /\
      Datatypes.length (sale_condition record) = 1 /\
      Datatypes.length (sale_condition_category record) = 1 /\
      (trade_price_short record < 256 ^ N.of_nat 2)%N /\
      (trade_volume_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (consolidated_high_low_last_indicator record) = 1 /\
      Datatypes.length (participant_open_high_low_last_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp131.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 5 (security_symbol_short record) ++
      encode_bytes 1 (sale_condition record) ++
      encode_bytes 1 (sale_condition_category record) ++
      encode_uint 2 (trade_price_short record) ++
      encode_uint 2 (trade_volume_short record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (consolidated_high_low_last_indicator record) ++
      encode_bytes 1 (participant_open_high_low_last_indicator record).

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
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (security_symbol_short_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (sale_condition_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sale_condition_category_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (trade_price_short_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (trade_volume_short_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (primary_listing_market_participant_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (consolidated_high_low_last_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (participant_open_high_low_last_indicator_value, bytes) =>
                                                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol_short := security_symbol_short_value; sale_condition := sale_condition_value; sale_condition_category := sale_condition_category_value; trade_price_short := trade_price_short_value; trade_volume_short := trade_volume_short_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; consolidated_high_low_last_indicator := consolidated_high_low_last_indicator_value; participant_open_high_low_last_indicator := participant_open_high_low_last_indicator_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !Timestamp131.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp131.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp131.eq_dec]. Defined.

  End ShortTradeMessage.

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

  Module SaleConditions8.

    (** Sale Conditions *)
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

  End SaleConditions8.

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

  Module ConsolidatedData2.

    (** Consolidated Data *)
    Record t := {
      previous_close_price_date : N;
      last_participant_id : list byte;
      last_price : N;
      high_price : N;
      low_price : N;
      total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_participant_id record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_participant_id_value, bytes) =>
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
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_participant_id := last_participant_id_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; total_volume := total_volume_value; tick := tick_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConsolidatedData2.

  Module ParticipantData2.

    (** Participant Data *)
    Record t := {
      previous_close_price_date : N;
      last_participant_id : list byte;
      last_price : N;
      high_price : N;
      low_price : N;
      total_volume : N;
      tick : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_close_price_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (last_participant_id record) = 1 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tick record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_close_price_date record) ++
      encode_bytes 1 (last_participant_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (total_volume record) ++
      encode_bytes 1 (tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_close_price_date_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_participant_id_value, bytes) =>
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
                              | Some (tick_value, bytes) =>
                                  Some ({| previous_close_price_date := previous_close_price_date_value; last_participant_id := last_participant_id_value; last_price := last_price_value; high_price := high_price_value; low_price := low_price_value; total_volume := total_volume_value; tick := tick_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParticipantData2.

  Module TradeCancelErrorMessage.

    (** The Trade Cancel/Error message is used cancel or error Cta eligible securities, Local Issues or Bond information. *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp132.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_conditions : SaleConditions8.t;
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
      consolidated_data : ConsolidatedData2.t;
      participant_data : ParticipantData2.t;
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
      SaleConditions8.bounded (sale_conditions record) /\
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
      ConsolidatedData2.bounded (consolidated_data record) /\
      ParticipantData2.bounded (participant_data record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp132.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleConditions8.encode (sale_conditions record) ++
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
      ConsolidatedData2.encode (consolidated_data record) ++
      ParticipantData2.encode (participant_data record).

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
                                  match SaleConditions8.decode bytes with
                                  | None => None
                                  | Some (sale_conditions_value, bytes) =>
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
                                                                                      match ConsolidatedData2.decode bytes with
                                                                                      | None => None
                                                                                      | Some (consolidated_data_value, bytes) =>
                                                                                          match ParticipantData2.decode bytes with
                                                                                          | None => None
                                                                                          | Some (participant_data_value, bytes) =>
                                                                                              Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; sale_conditions := sale_conditions_value; trade_price := trade_price_value; trade_volume := trade_volume_value; sellers_sale_days := sellers_sale_days_value; stop_stock_indicator := stop_stock_indicator_value; trade_through_exempt_indicator := trade_through_exempt_indicator_value; trade_reporting_facility_id := trade_reporting_facility_id_value; original_participant_reference_number := original_participant_reference_number_value; timestamp_2 := timestamp_2_value; cancel_error_action := cancel_error_action_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; consolidated_data := consolidated_data_value; participant_data := participant_data_value |}, bytes)
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 150.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp132.encode_length, !encode_uint_length, !SaleConditions8.encode_length, !Timestamp23.encode_length, !ConsolidatedData2.encode_length, !ParticipantData2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp132.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite SaleConditions8.decode_encode by exact bound_7.
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
      rewrite ConsolidatedData2.decode_encode by exact bound_20.
      rewrite ParticipantData2.decode_encode by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp132.eq_dec | apply SaleConditions8.eq_dec | apply Timestamp23.eq_dec | apply ConsolidatedData2.eq_dec | apply ParticipantData2.eq_dec]. Defined.

  End TradeCancelErrorMessage.

End SiacCtsOutputV191.
