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

    License: MIT No Attribution
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

  Module EndOfEndOfDaySummaryMessage.

    (** Used to signal the end of Consolidated End of Day Summary and Participant End of Day Summary message iterations *)
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

  End EndOfEndOfDaySummaryMessage.

  Module StartOfStartOfDaySummaryMessage.

    (** Used to signal the start of Start of Day Summary message iterations *)
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

  End StartOfStartOfDaySummaryMessage.

  Module EndOfStartOfDaySummaryMessage.

    (** Used to signal the end of Start of Day Summary message iterations *)
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

  End EndOfStartOfDaySummaryMessage.

  Module SymbolReferenceDataMessage.

    (** Symbol Reference Data message *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End SymbolReferenceDataMessage.

  Module StartOfDayMessage.

    (** Signals the start of normal data dissemination over the multicast lines *)
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

  End StartOfDayMessage.

  Module ResetBlockSequenceNumberMessage.

    (** Transmitted when the Block Sequence Number on an output multicast line requires resetting *)
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

  End ResetBlockSequenceNumberMessage.

  Module DisasterRecoveryDataCenterActivationMessage.

    (** Signifies that the Consolidated Tape System has switched processing from the Primary Data Center to the Disaster Recovery Data Center *)
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

  End DisasterRecoveryDataCenterActivationMessage.

  Module LineIntegrityMessage.

    (** Transmitted over the multicast lines at frequent intervals to verify continued integrity of multicast transmission *)
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

  End LineIntegrityMessage.

  Module EndOfDayMessage.

    (** Transmitted over the multicast lines to advise all Data Recipients that there are no further messages to be transmitted for the day *)
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

  End EndOfDayMessage.

  Module IndexMessage.

    (** The Index message contains the index and the index value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      index_symbol : list byte;
      index_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (index_symbol record) = 11 /\
      (index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (index_symbol record) ++
      encode_uint 8 (index_value record).

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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End IndexMessage.

  Module BidAndOfferIndexMessage.

    (** The Bid and Offer Index message contains the index Bid and Offer index values *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (index_symbol record) = 11 /\
      (bid_index_value record < 256 ^ N.of_nat 8)%N /\
      (offer_index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End BidAndOfferIndexMessage.

  Module MarketWideCircuitBreakerDeclineLevelStatusMessage.

    (** Reports the calculated Level 1, Level 2 and Level 3 threshold values for the current trading day necessary to trigger a circuit breaker *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End MarketWideCircuitBreakerDeclineLevelStatusMessage.

  Module MarketWideCircuitBreakerStatusMessage.

    (** Reports the Market-Wide Circuit Breaker threshold Level that has been breached *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      market_wide_circuit_breaker_level_indicator : list byte;
      reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_wide_circuit_breaker_level_indicator record) = 1 /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 1 (market_wide_circuit_breaker_level_indicator record) ++
      encode_bytes 1 (reserved record).

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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End MarketWideCircuitBreakerStatusMessage.

  Module ApproximateTradesAndTotalDollarValueMessage.

    (** Allows a Participant to report the total trades and total dollar value of trades at their respective market centers *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      total_trades : N;
      dollar_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (total_trades record < 256 ^ N.of_nat 4)%N /\
      (dollar_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_uint 4 (total_trades record) ++
      encode_uint 8 (dollar_value record).

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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End ApproximateTradesAndTotalDollarValueMessage.

  Module CrossingSessionSummaryMessage.

    (** Used to report the total volume and dollar value of trades transacted after the close of a Participant's regular session *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_i_total_trades_volume record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_ii_dollar_value record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_ii_total_trades_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End CrossingSessionSummaryMessage.

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
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !CorrectedPriorDayTradeDateAndTime.encode_length, !OriginalPriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 bound_23]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply CorrectedPriorDayTradeDateAndTime.eq_dec | apply OriginalPriorDayTradeDateAndTime.eq_dec]. Defined.

  End PriorDayTradeCorrectionMessage.

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
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !PriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply PriorDayTradeDateAndTime.eq_dec]. Defined.

  End PriorDayTradeMessage.

  Module PriorDayTradeCancelErrorMessage.

    (** Used to report the cancellation of a trade or error a trade that never took place but was reported, for transactions originally reported earlier than the current day. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      cancel_error_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp1.bounded (timestamp_1 record) /\
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
      PriorDayTradeDateAndTime.bounded (prior_day_trade_date_and_time record) /\
      Datatypes.length (cancel_error_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
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
      PriorDayTradeDateAndTime.encode (prior_day_trade_date_and_time record) ++
      encode_bytes 1 (cancel_error_action record).

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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !PriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply PriorDayTradeDateAndTime.eq_dec]. Defined.

  End PriorDayTradeCancelErrorMessage.

  Module FractionalPriorDayTradeCorrectionMessage.

    (** Used to correct a transaction originally reported on a trading day earlier than the current trading day. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition4.t;
      trade_price : N;
      fractional_trade_volume : N;
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
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition4.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition4.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
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
                                                                  match PriorDayTradeDateAndTime.decode bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !PriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply PriorDayTradeDateAndTime.eq_dec]. Defined.

  End FractionalPriorDayTradeCorrectionMessage.

  Module FractionalPriorDayTradeMessage.

    (** Used to report a CTA Equity, Local Issue or Bond transaction which occurred earlier than the current trading day and was not reported. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition4.t;
      trade_price : N;
      fractional_trade_volume : N;
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
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition4.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime.bounded (prior_day_trade_date_and_time record).

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition4.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
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
                                                                  match PriorDayTradeDateAndTime.decode bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !PriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply PriorDayTradeDateAndTime.eq_dec]. Defined.

  End FractionalPriorDayTradeMessage.

  Module FractionalPriorDayTradeCancelErrorMessage.

    (** Used to report the cancellation of a trade or error a trade that never took place but was reported, for transactions originally reported earlier than the current day. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition4.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      trade_reporting_facility_id : list byte;
      prior_day_trade_date_and_time : PriorDayTradeDateAndTime.t;
      cancel_error_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition4.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      PriorDayTradeDateAndTime.bounded (prior_day_trade_date_and_time record) /\
      Datatypes.length (cancel_error_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition4.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      PriorDayTradeDateAndTime.encode (prior_day_trade_date_and_time record) ++
      encode_bytes 1 (cancel_error_action record).

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
                                                                  match PriorDayTradeDateAndTime.decode bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !PriorDayTradeDateAndTime.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply PriorDayTradeDateAndTime.eq_dec]. Defined.

  End FractionalPriorDayTradeCancelErrorMessage.

  Module ConsolidatedStartOfDaySummaryMessage.

    (** Provides, by security, consolidated previous close price and previous close price date information for CTA eligible Equity, Local Issues and Bonds *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End ConsolidatedStartOfDaySummaryMessage.

  Module ParticipantStartOfDaySummaryMessage.

    (** Provides, by security, Participant previous close price and previous close price date information for CTA eligible Equity, Local Issues and Bonds *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End ParticipantStartOfDaySummaryMessage.

  Module ConsolidatedEndOfDaySummaryMessage.

    (** Provides by security, the Consolidated High, Low, Last and Volume for CTA eligible Equity, Local Issues and Bonds. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End ConsolidatedEndOfDaySummaryMessage.

  Module FractionalConsolidatedEndOfDaySummaryMessage.

    (** Provides by security, the Consolidated High, Low, Last and Volume for CTA eligible Equity, Local Issues and Bonds. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End FractionalConsolidatedEndOfDaySummaryMessage.

  Module ParticipantEndOfDaySummaryMessage.

    (** Provides by security, the Participant Open, High, Low, Last, Volume and Tick information for CTA eligible securities, Local Issues and Bonds. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End ParticipantEndOfDaySummaryMessage.

  Module FractionalParticipantEndOfDaySummaryMessage.

    (** Provides by security, the Participant Open, High, Low, Last, Volume and Tick information for CTA eligible securities, Local Issues and Bonds. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End FractionalParticipantEndOfDaySummaryMessage.

  Module AuctionStatusMessage.

    (** Used when a Participant in a CTA eligible security, Local Issue or a Bond requires Auction Information *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End AuctionStatusMessage.

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
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !Timestamp2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 bound_39]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply Timestamp2.eq_dec]. Defined.

  End TradeCorrectionMessage.

  Module LongTradeMessage.

    (** Used to report trade information for CTA eligible Equity, Local Issue or Bonds. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      trade_reporting_facility_id : list byte;
      timestamp_2 : Timestamp2.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      Timestamp2.bounded (timestamp_2 record) /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (held_trade_indicator record) = 1 /\
      Datatypes.length (consolidated_high_low_last_indicator record) = 1 /\
      Datatypes.length (participant_open_high_low_last_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
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
      encode_bytes 1 (trade_reporting_facility_id record) ++
      Timestamp2.encode (timestamp_2 record) ++
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
                                                          | Some (trade_reporting_facility_id_value, bytes) =>
                                                              match Timestamp2.decode bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !Timestamp2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
      rewrite Timestamp2.decode_encode by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply Timestamp2.eq_dec]. Defined.

  End LongTradeMessage.

  Module ShortTradeMessage.

    (** Used to report trade information for CTA eligible Equity only. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End ShortTradeMessage.

  Module TradeCancelErrorMessage.

    (** Used to cancel or error CTA eligible securities, Local Issues or Bond information. To be descoped when Fractional Trade Volume publication is activated *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      trade_reporting_facility_id : list byte;
      original_participant_reference_number : N;
      timestamp_2 : Timestamp2.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      (original_participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Timestamp2.bounded (timestamp_2 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      encode_bytes 1 (trade_reporting_facility_id record) ++
      encode_uint 8 (original_participant_reference_number record) ++
      Timestamp2.encode (timestamp_2 record) ++
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
                                                          | Some (trade_reporting_facility_id_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (original_participant_reference_number_value, bytes) =>
                                                                  match Timestamp2.decode bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !Timestamp2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 bound_33]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
      rewrite decode_encode_uint by exact bound_14.
      rewrite Timestamp2.decode_encode by exact bound_15.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply Timestamp2.eq_dec]. Defined.

  End TradeCancelErrorMessage.

  Module FractionalTradeCorrectionMessage.

    (** Used to correct CTA eligible Equity, Local Issue or Bond information. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      timestamp_2 : Timestamp2.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp2.bounded (timestamp_2 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      Timestamp2.encode (timestamp_2 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !Timestamp2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 bound_39]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply Timestamp2.eq_dec]. Defined.

  End FractionalTradeCorrectionMessage.

  Module FractionalLongTradeMessage.

    (** Used to report trade information for CTA eligible Equity, Local Issue or Bonds. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition4.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      trade_reporting_facility_id : list byte;
      timestamp_2 : Timestamp2.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition4.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      Timestamp2.bounded (timestamp_2 record) /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (held_trade_indicator record) = 1 /\
      Datatypes.length (consolidated_high_low_last_indicator record) = 1 /\
      Datatypes.length (participant_open_high_low_last_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition4.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      Timestamp2.encode (timestamp_2 record) ++
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
                                                              match Timestamp2.decode bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !Timestamp2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 bound_20]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
      rewrite Timestamp2.decode_encode by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply Timestamp2.eq_dec]. Defined.

  End FractionalLongTradeMessage.

  Module TradingStatusMessage.

    (** Transmitted when a Participant in a CTA eligible security, Local Issue or a Bond elects to notify CTS of a Trading Halt, a Trading Resume, a Price Indication or a Market Imbalance *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End TradingStatusMessage.

  Module FractionalShortTradeMessage.

    (** Used to report trade information for CTA eligible Equity only. Volume is represented as a fractional value. Not published by CTS currently, message type is reserved for future use *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec]. Defined.

  End FractionalShortTradeMessage.

  Module FractionalTradeCancelErrorMessage.

    (** Used to cancel or error CTA eligible securities, Local Issues or Bond information. Volume is represented as a fractional value *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp1.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      security_symbol : list byte;
      instrument_type : list byte;
      sale_condition_4 : SaleCondition4.t;
      trade_price : N;
      fractional_trade_volume : N;
      sellers_sale_days : N;
      stop_stock_indicator : list byte;
      trade_through_exempt_indicator : list byte;
      trade_reporting_facility_id : list byte;
      original_participant_reference_number : N;
      timestamp_2 : Timestamp2.t;
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
      Timestamp1.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      SaleCondition4.bounded (sale_condition_4 record) /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (fractional_trade_volume record < 256 ^ N.of_nat 8)%N /\
      (sellers_sale_days record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stop_stock_indicator record) = 1 /\
      Datatypes.length (trade_through_exempt_indicator record) = 1 /\
      Datatypes.length (trade_reporting_facility_id record) = 1 /\
      (original_participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Timestamp2.bounded (timestamp_2 record) /\
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
      Timestamp1.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      SaleCondition4.encode (sale_condition_4 record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (fractional_trade_volume record) ++
      encode_uint 1 (sellers_sale_days record) ++
      encode_bytes 1 (stop_stock_indicator record) ++
      encode_bytes 1 (trade_through_exempt_indicator record) ++
      encode_bytes 1 (trade_reporting_facility_id record) ++
      encode_uint 8 (original_participant_reference_number record) ++
      Timestamp2.encode (timestamp_2 record) ++
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
                                                                  match Timestamp2.decode bytes with
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
      rewrite !length_app, !encode_bytes_length, !Timestamp1.encode_length, !encode_uint_length, !SaleCondition4.encode_length, !Timestamp2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 bound_33]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp1.decode_encode by exact bound_1.
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
      rewrite decode_encode_uint by exact bound_14.
      rewrite Timestamp2.decode_encode by exact bound_15.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp1.eq_dec | apply SaleCondition4.eq_dec | apply Timestamp2.eq_dec]. Defined.

  End FractionalTradeCancelErrorMessage.

End SiacCtsOutputV211B.
