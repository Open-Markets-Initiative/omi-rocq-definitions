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
      - a Reassemble rule
      - a run counted by a field
      - a Composite rule
  *)

Module SiacCtsInputV27F.

  Module BlockHeader.

    (** Cta participant input block header *)
    Record t := {
      version : N;
      block_size : N;
      block_sequence_number : N;
      messages_in_block : N;
      block_checksum : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (version record < 256 ^ N.of_nat 1)%N /\
      (block_size record < 256 ^ N.of_nat 2)%N /\
      (block_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (messages_in_block record < 256 ^ N.of_nat 1)%N /\
      (block_checksum record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (version record) ++
      encode_uint 2 (block_size record) ++
      encode_uint 4 (block_sequence_number record) ++
      encode_uint 1 (messages_in_block record) ++
      encode_uint 2 (block_checksum record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (version_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (block_size_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (block_sequence_number_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (messages_in_block_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (block_checksum_value, bytes) =>
                          Some ({| version := version_value; block_size := block_size_value; block_sequence_number := block_sequence_number_value; messages_in_block := messages_in_block_value; block_checksum := block_checksum_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BlockHeader.

  Module RejectionMessage.

    (** Used for all errors to notify a Participant that CTS has found an error in the Block Header, Message Header or Message body of a Participant Input message. *)
    Record t := {
      error_code : N;
      block_sequence_number : N;
      participant_reference_number : N;
      message_i_d : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (error_code record < 256 ^ N.of_nat 1)%N /\
      (block_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (message_i_d record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (error_code record) ++
      encode_uint 4 (block_sequence_number record) ++
      encode_uint 8 (participant_reference_number record) ++
      encode_uint 1 (message_i_d record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (error_code_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (block_sequence_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (participant_reference_number_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (message_i_d_value, bytes) =>
                      Some ({| error_code := error_code_value; block_sequence_number := block_sequence_number_value; participant_reference_number := participant_reference_number_value; message_i_d := message_i_d_value |}, bytes)
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

  End RejectionMessage.

  Module WarningMessage.

    (** Sent from CTS to a Participant in response to a Block Sequence Number Gap. The block will still be processed by CTS. *)
    Record t := {
      previous_block_sequence_number : N;
      previous_participant_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (previous_block_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (previous_participant_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (previous_block_sequence_number record) ++
      encode_uint 8 (previous_participant_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (previous_block_sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (previous_participant_reference_number_value, bytes) =>
              Some ({| previous_block_sequence_number := previous_block_sequence_number_value; previous_participant_reference_number := previous_participant_reference_number_value |}, bytes)
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

  End WarningMessage.

  Module SequenceInformationAndMessageCountResponseMessage.

    (** Generated by CTS to a Participant in response to a Sequence Information and Message Count Inquiry message. Transmitted in a separate block. *)
    Record t := {
      current_block_sequence_number : N;
      last_participant_reference_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (current_block_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (last_participant_reference_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (current_block_sequence_number record) ++
      encode_uint 8 (last_participant_reference_number record) ++
      encode_uint 8 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (current_block_sequence_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (last_participant_reference_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| current_block_sequence_number := current_block_sequence_number_value; last_participant_reference_number := last_participant_reference_number_value; message_count := message_count_value |}, bytes)
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

  End SequenceInformationAndMessageCountResponseMessage.

  Module TestMessage.

    (** Generated by CTS or a Participant to exercise the line and verify transmission integrity. Transmitted as the only message in a block. *)
    Record t := {
      data : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (data record) = 256.

    Definition encode (record : t) : list byte :=
      encode_bytes 256 (data record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 256 bytes with
      | None => None
      | Some (data_value, bytes) =>
          Some ({| data := data_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 256.
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

  End TestMessage.

  Module IndexMessage.

    (** Contains the index and the index value. *)
    Record t := {
      index_symbol : list byte;
      index_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_symbol record) = 11 /\
      (index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (index_symbol record) ++
      encode_uint 8 (index_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (index_symbol_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (index_value_value, bytes) =>
              Some ({| index_symbol := index_symbol_value; index_value := index_value_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexMessage.

  Module BidAndOfferIndexMessage.

    (** Contains the Bid and Offer index values. *)
    Record t := {
      index_symbol : list byte;
      bid_index_value : N;
      offer_index_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_symbol record) = 11 /\
      (bid_index_value record < 256 ^ N.of_nat 8)%N /\
      (offer_index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (index_symbol record) ++
      encode_uint 8 (bid_index_value record) ++
      encode_uint 8 (offer_index_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (index_symbol_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (bid_index_value_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (offer_index_value_value, bytes) =>
                  Some ({| index_symbol := index_symbol_value; bid_index_value := bid_index_value_value; offer_index_value := offer_index_value_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidAndOfferIndexMessage.

  Module ApproximateTradesAndTotalDollarValueMessage.

    (** Allows a Participant to report the total trades and total dollar value of trades at their respective market centers. *)
    Record t := {
      total_trades : N;
      dollar_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (total_trades record < 256 ^ N.of_nat 4)%N /\
      (dollar_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (total_trades record) ++
      encode_uint 8 (dollar_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (total_trades_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (dollar_value_value, bytes) =>
              Some ({| total_trades := total_trades_value; dollar_value := dollar_value_value |}, bytes)
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

  End ApproximateTradesAndTotalDollarValueMessage.

  Module CrossingSessionMessage.

    (** Used to report the total volume and dollar value of trades transacted after the close of a Participant's regular session. *)
    Record t := {
      crossing_session_i_total_trades_volume : N;
      crossing_session_ii_dollar_value : N;
      crossing_session_ii_total_trades_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (crossing_session_i_total_trades_volume record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_ii_dollar_value record < 256 ^ N.of_nat 8)%N /\
      (crossing_session_ii_total_trades_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (crossing_session_i_total_trades_volume record) ++
      encode_uint 8 (crossing_session_ii_dollar_value record) ++
      encode_uint 8 (crossing_session_ii_total_trades_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (crossing_session_i_total_trades_volume_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (crossing_session_ii_dollar_value_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (crossing_session_ii_total_trades_volume_value, bytes) =>
                  Some ({| crossing_session_i_total_trades_volume := crossing_session_i_total_trades_volume_value; crossing_session_ii_dollar_value := crossing_session_ii_dollar_value_value; crossing_session_ii_total_trades_volume := crossing_session_ii_total_trades_volume_value |}, bytes)
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

  End CrossingSessionMessage.

  Module AuctionStatusMessage.

    (** Transmitted when a Participant in a CTA eligible security requires Auction Information. Initial Auction Collar is published after the LULD Trading Pause. *)
    Record t := {
      security_symbol : list byte;
      instrument_type : list byte;
      auction_collar_reference_price : N;
      auction_collar_upper_threshold_price : N;
      auction_collar_lower_threshold_price : N;
      number_of_extensions : N;
      reserved_62 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      (auction_collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_upper_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_lower_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (number_of_extensions record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reserved_62 record) = 62.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_uint 8 (auction_collar_reference_price record) ++
      encode_uint 8 (auction_collar_upper_threshold_price record) ++
      encode_uint 8 (auction_collar_lower_threshold_price record) ++
      encode_uint 1 (number_of_extensions record) ++
      encode_bytes 62 (reserved_62 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                              match decode_bytes 62 bytes with
                              | None => None
                              | Some (reserved_62_value, bytes) =>
                                  Some ({| security_symbol := security_symbol_value; instrument_type := instrument_type_value; auction_collar_reference_price := auction_collar_reference_price_value; auction_collar_upper_threshold_price := auction_collar_upper_threshold_price_value; auction_collar_lower_threshold_price := auction_collar_lower_threshold_price_value; number_of_extensions := number_of_extensions_value; reserved_62 := reserved_62_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 99.
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

  End AuctionStatusMessage.

  Module TradingStatusMessage.

    (** Allows a Participant that is the listing exchange to notify CTS of Trading Halts, Resumes, Indications, Imbalances, Short Sale Restriction Indicators and LULD Reference Prices. Bidirectional. *)
    Record t := {
      security_symbol : list byte;
      instrument_type : list byte;
      last_price_opening_reopening_luld_reference_price : N;
      high_indication_price_upper_limit_price_band : N;
      low_indication_price_lower_limit_price_band : N;
      buy_volume : N;
      sell_volume : N;
      security_status : list byte;
      halt_reason : list byte;
      short_sale_restriction_indicator : list byte;
      trading_status_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      (last_price_opening_reopening_luld_reference_price record < 256 ^ N.of_nat 8)%N /\
      (high_indication_price_upper_limit_price_band record < 256 ^ N.of_nat 8)%N /\
      (low_indication_price_lower_limit_price_band record < 256 ^ N.of_nat 8)%N /\
      (buy_volume record < 256 ^ N.of_nat 4)%N /\
      (sell_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_status record) = 1 /\
      Datatypes.length (halt_reason record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      (trading_status_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_uint 8 (last_price_opening_reopening_luld_reference_price record) ++
      encode_uint 8 (high_indication_price_upper_limit_price_band record) ++
      encode_uint 8 (low_indication_price_lower_limit_price_band record) ++
      encode_uint 4 (buy_volume record) ++
      encode_uint 4 (sell_volume record) ++
      encode_bytes 1 (security_status record) ++
      encode_bytes 1 (halt_reason record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_uint 4 (trading_status_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (security_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (instrument_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_price_opening_reopening_luld_reference_price_value, bytes) =>
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
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (trading_status_id_value, bytes) =>
                                                  Some ({| security_symbol := security_symbol_value; instrument_type := instrument_type_value; last_price_opening_reopening_luld_reference_price := last_price_opening_reopening_luld_reference_price_value; high_indication_price_upper_limit_price_band := high_indication_price_upper_limit_price_band_value; low_indication_price_lower_limit_price_band := low_indication_price_lower_limit_price_band_value; buy_volume := buy_volume_value; sell_volume := sell_volume_value; security_status := security_status_value; halt_reason := halt_reason_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; trading_status_id := trading_status_id_value |}, bytes)
                                              end
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module ShortTradeMessage.

    (** Reports trade information for CTA eligible Equity, Local Issues or Bonds when the trade meets all criteria for the compact Short format; otherwise the Long Trade message is used. *)
    Record t := {
      security_symbol_short : list byte;
      sale_condition_short : list byte;
      sale_condition_category : list byte;
      trade_price_short : N;
      trade_volume_short : N;
      reserved_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (security_symbol_short record) = 5 /\
      Datatypes.length (sale_condition_short record) = 1 /\
      Datatypes.length (sale_condition_category record) = 1 /\
      (trade_price_short record < 256 ^ N.of_nat 2)%N /\
      (trade_volume_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (reserved_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (security_symbol_short record) ++
      encode_bytes 1 (sale_condition_short record) ++
      encode_bytes 1 (sale_condition_category record) ++
      encode_uint 2 (trade_price_short record) ++
      encode_uint 2 (trade_volume_short record) ++
      encode_bytes 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (security_symbol_short_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sale_condition_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sale_condition_category_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (trade_price_short_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (trade_volume_short_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (reserved_3_value, bytes) =>
                              Some ({| security_symbol_short := security_symbol_short_value; sale_condition_short := sale_condition_short_value; sale_condition_category := sale_condition_category_value; trade_price_short := trade_price_short_value; trade_volume_short := trade_volume_short_value; reserved_3 := reserved_3_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortTradeMessage.

  Module FractionalShortTradeMessage.

    (** Reports trade information with fractional volume when the trade meets all criteria for the compact Short format; otherwise the Long Trade or Fractional Long Trade message is used. *)
    Record t := {
      security_symbol_short : list byte;
      sale_condition_short : list byte;
      sale_condition_category : list byte;
      trade_price_short : N;
      fractional_trade_volume_short : N;
      reserved_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (security_symbol_short record) = 5 /\
      Datatypes.length (sale_condition_short record) = 1 /\
      Datatypes.length (sale_condition_category record) = 1 /\
      (trade_price_short record < 256 ^ N.of_nat 2)%N /\
      (fractional_trade_volume_short record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (security_symbol_short record) ++
      encode_bytes 1 (sale_condition_short record) ++
      encode_bytes 1 (sale_condition_category record) ++
      encode_uint 2 (trade_price_short record) ++
      encode_uint 4 (fractional_trade_volume_short record) ++
      encode_bytes 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (security_symbol_short_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sale_condition_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sale_condition_category_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (trade_price_short_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (fractional_trade_volume_short_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (reserved_3_value, bytes) =>
                              Some ({| security_symbol_short := security_symbol_short_value; sale_condition_short := sale_condition_short_value; sale_condition_category := sale_condition_category_value; trade_price_short := trade_price_short_value; fractional_trade_volume_short := fractional_trade_volume_short_value; reserved_3 := reserved_3_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalShortTradeMessage.

End SiacCtsInputV27F.
