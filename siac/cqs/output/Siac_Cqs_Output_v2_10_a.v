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
      - a field present only on a condition
  *)

Module SiacCqsOutputV210A.

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

  Module SymbolReferenceDataMessage.

    (** Symbol Reference Data Message *)
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
      reserved : list byte;
      luld_tier : list byte;
      luld_leverage_ratio : N;
      test : list byte;
      ipo : list byte;
      financial_status_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      halt_reason : list byte;
      instrument_type : list byte;
      second_reserved : list byte;
      third_reserved : list byte;
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
      Datatypes.length (reserved record) = 1 /\
      Datatypes.length (luld_tier record) = 1 /\
      (luld_leverage_ratio record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (test record) = 1 /\
      Datatypes.length (ipo record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (halt_reason record) = 1 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (second_reserved record) = 1 /\
      Datatypes.length (third_reserved record) = 1 /\
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
      encode_bytes 1 (reserved record) ++
      encode_bytes 1 (luld_tier record) ++
      encode_uint 4 (luld_leverage_ratio record) ++
      encode_bytes 1 (test record) ++
      encode_bytes 1 (ipo record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (halt_reason record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (second_reserved record) ++
      encode_bytes 1 (third_reserved record) ++
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
                                                  | Some (reserved_value, bytes) =>
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
                                                                                      | Some (second_reserved_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (third_reserved_value, bytes) =>
                                                                                              match decode_bytes 128 bytes with
                                                                                              | None => None
                                                                                              | Some (reserved_128_value, bytes) =>
                                                                                                  Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value; security_symbol := security_symbol_value; prior_security_symbol := prior_security_symbol_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; primary_listing_market_previous_closing_price := primary_listing_market_previous_closing_price_value; consolidated_closing_price := consolidated_closing_price_value; round_lot_size := round_lot_size_value; reserved := reserved_value; luld_tier := luld_tier_value; luld_leverage_ratio := luld_leverage_ratio_value; test := test_value; ipo := ipo_value; financial_status_indicator := financial_status_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; halt_reason := halt_reason_value; instrument_type := instrument_type_value; second_reserved := second_reserved_value; third_reserved := third_reserved_value; reserved_128 := reserved_128_value |}, bytes)
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

  Module StartOfDayMessage.

    (** Start of Day Message *)
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

  End StartOfDayMessage.

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

  Module FinraCloseMessage.

    (** FINRA Close Message *)
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

  End FinraCloseMessage.

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

  Module ResetBlockSequenceNumberMessage.

    (** Reset Block Sequence Number Message *)
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

  End ResetBlockSequenceNumberMessage.

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

  Module FinraOpenMessage.

    (** FINRA Open Message *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp15.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp15.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp15.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record).

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
                          Some ({| participant_id := participant_id_value; timestamp_1 := timestamp_1_value; message_id := message_id_value; transaction_id := transaction_id_value; participant_reference_number := participant_reference_number_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Timestamp15.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp15.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp15.eq_dec]. Defined.

  End FinraOpenMessage.

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

  Module DisasterRecoveryDataCenterActivationMessage.

    (** Disaster Recovery Data Center Activation Message *)
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

  End DisasterRecoveryDataCenterActivationMessage.

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

  Module LineIntegrityMessage.

    (** Line Integrity Message *)
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

  End LineIntegrityMessage.

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

  Module EndOfDayMessage.

    (** End of Day Message *)
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

  End EndOfDayMessage.

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

  Module MarketWideCircuitBreakerDeclineLevelStatusMessage.

    (** Reports the calculated Level 1, Level 2 and Level 3 threshold values for the current trading day necessary to trigger a circuit breaker *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp19.t;
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
      Timestamp19.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp19.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp19.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp19.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp19.eq_dec]. Defined.

  End MarketWideCircuitBreakerDeclineLevelStatusMessage.

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

  Module MarketWideCircuitBreakerStatusMessage.

    (** Reports the Market-Wide Circuit Breaker threshold Level that has been breached *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp110.t;
      message_id : N;
      transaction_id : N;
      participant_reference_number : N;
      market_wide_circuit_breaker_level_indicator : list byte;
      reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Timestamp110.bounded (timestamp_1 record) /\
      (message_id record < 256 ^ N.of_nat 1)%N /\
      (transaction_id record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_wide_circuit_breaker_level_indicator record) = 1 /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      Timestamp110.encode (timestamp_1 record) ++
      encode_uint 1 (message_id record) ++
      encode_uint 4 (transaction_id record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_bytes 1 (market_wide_circuit_breaker_level_indicator record) ++
      encode_bytes 1 (reserved record).

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
      rewrite !length_app, !encode_bytes_length, !Timestamp110.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp110.decode_encode by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp110.eq_dec]. Defined.

  End MarketWideCircuitBreakerStatusMessage.

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

  Module AuctionStatusMessage.

    (** Used when a Participant in a CTA eligible security, Local Issue or Bonds reports requires Auction Information *)
    Record t := {
      participant_id : list byte;
      timestamp_1 : Timestamp111.t;
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
      Timestamp111.bounded (timestamp_1 record) /\
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
      Timestamp111.encode (timestamp_1 record) ++
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
      rewrite !length_app, !encode_bytes_length, !Timestamp111.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite Timestamp111.decode_encode by exact bound_1.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp111.eq_dec]. Defined.

  End AuctionStatusMessage.

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

End SiacCqsOutputV210A.
