From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Output

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
      - the dispatch that chooses a message by its type
      - a run counted by a field
      - a field present only on a condition
      - a length prefix framing what follows
  *)

Module NasdaqUqdfOutputV30C.

  Module PacketHeader.

    (** Utp Mold Udp 64 Packet Header *)
    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End PacketHeader.

  Module MessageHeader.

    (** Utp Mold Udp 64 Message Header *)
    Record t := {
      message_length : N;
      version : list byte;
      message_category : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (version record) = 1 /\
      Datatypes.length (message_category record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (version record) ++
      encode_bytes 1 (message_category record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (version_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_category_value, bytes) =>
                  Some ({| message_length := message_length_value; version := version_value; message_category := message_category_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module FinraAdfMarketParticipantQuotationMessage.

    (** FINRA ADF Quotation Message. Sent for FINRA quotes that do not affect the NBBO or FINRA BBO. May also be produced when the FINRA BBO quote impacts either the current FINRA best bid or best ask. *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      timestamp_2 : N;
      symbol_long : list byte;
      bid_price_long : N;
      bid_size_long : N;
      ask_price_long : N;
      ask_size_long : N;
      quote_condition : list byte;
      finra_market_participant : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      (timestamp_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (bid_price_long record < 256 ^ N.of_nat 8)%N /\
      (bid_size_long record < 256 ^ N.of_nat 4)%N /\
      (ask_price_long record < 256 ^ N.of_nat 8)%N /\
      (ask_size_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      Datatypes.length (finra_market_participant record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_uint 8 (timestamp_2 record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 8 (bid_price_long record) ++
      encode_uint 4 (bid_size_long record) ++
      encode_uint 8 (ask_price_long record) ++
      encode_uint 4 (ask_size_long record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_bytes 4 (finra_market_participant record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (timestamp_2_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (symbol_long_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (bid_price_long_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (bid_size_long_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (ask_price_long_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (ask_size_long_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (quote_condition_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (finra_market_participant_value, bytes) =>
                                                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; timestamp_2 := timestamp_2_value; symbol_long := symbol_long_value; bid_price_long := bid_price_long_value; bid_size_long := bid_size_long_value; ask_price_long := ask_price_long_value; ask_size_long := ask_size_long_value; quote_condition := quote_condition_value; finra_market_participant := finra_market_participant_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FinraAdfMarketParticipantQuotationMessage.

  Module CrossSroTradingActionMessage.

    (** Informs subscribers of trading actions (halts, pauses, quotation resumptions and trading resumptions) impacting the trading of a NASDAQ-listed issue across all UTP participants *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol_long : list byte;
      trading_action_code : list byte;
      trading_action_sequence_number : N;
      action_time : N;
      reason_for_the_trading_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (trading_action_code record) = 1 /\
      (trading_action_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (action_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reason_for_the_trading_action record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (trading_action_code record) ++
      encode_uint 4 (trading_action_sequence_number record) ++
      encode_uint 8 (action_time record) ++
      encode_bytes 6 (reason_for_the_trading_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trading_action_code_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (trading_action_sequence_number_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (action_time_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (reason_for_the_trading_action_value, bytes) =>
                                              Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol_long := symbol_long_value; trading_action_code := trading_action_code_value; trading_action_sequence_number := trading_action_sequence_number_value; action_time := action_time_value; reason_for_the_trading_action := reason_for_the_trading_action_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CrossSroTradingActionMessage.

  Module MarketCenterTradingActionMessage.

    (** Informs UTP data feed subscribers when a UTP participant invokes or releases a market center-specific trading halt for a NASDAQ-listed security *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol_long : list byte;
      trading_action_code : list byte;
      action_time : N;
      market_center_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (trading_action_code record) = 1 /\
      (action_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_center_identifier record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (trading_action_code record) ++
      encode_uint 8 (action_time record) ++
      encode_bytes 1 (market_center_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trading_action_code_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (action_time_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (market_center_identifier_value, bytes) =>
                                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol_long := symbol_long_value; trading_action_code := trading_action_code_value; action_time := action_time_value; market_center_identifier := market_center_identifier_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketCenterTradingActionMessage.

  Module IssueSymbolDirectoryMessage.

    (** Issue Symbol Directory Message providing reference data for NASDAQ-listed securities *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol_long : list byte;
      old_symbol : list byte;
      issue_name : list byte;
      issue_type : list byte;
      issue_subtype : list byte;
      market_tier : list byte;
      authenticity : list byte;
      short_sale_threshold_indicator : list byte;
      round_lot_size : N;
      financial_status_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (old_symbol record) = 11 /\
      Datatypes.length (issue_name record) = 30 /\
      Datatypes.length (issue_type record) = 1 /\
      Datatypes.length (issue_subtype record) = 2 /\
      Datatypes.length (market_tier record) = 1 /\
      Datatypes.length (authenticity record) = 1 /\
      Datatypes.length (short_sale_threshold_indicator record) = 1 /\
      (round_lot_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (financial_status_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 11 (old_symbol record) ++
      encode_bytes 30 (issue_name record) ++
      encode_bytes 1 (issue_type record) ++
      encode_bytes 2 (issue_subtype record) ++
      encode_bytes 1 (market_tier record) ++
      encode_bytes 1 (authenticity record) ++
      encode_bytes 1 (short_sale_threshold_indicator record) ++
      encode_uint 2 (round_lot_size record) ++
      encode_bytes 1 (financial_status_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (old_symbol_value, bytes) =>
                                  match decode_bytes 30 bytes with
                                  | None => None
                                  | Some (issue_name_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (issue_type_value, bytes) =>
                                          match decode_bytes 2 bytes with
                                          | None => None
                                          | Some (issue_subtype_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (market_tier_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (authenticity_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (short_sale_threshold_indicator_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (round_lot_size_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (financial_status_indicator_value, bytes) =>
                                                                  Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol_long := symbol_long_value; old_symbol := old_symbol_value; issue_name := issue_name_value; issue_type := issue_type_value; issue_subtype := issue_subtype_value; market_tier := market_tier_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; round_lot_size := round_lot_size_value; financial_status_indicator := financial_status_indicator_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 87.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IssueSymbolDirectoryMessage.

  Module RegShoShortSalePriceTestRestrictedIndicatorMessage.

    (** Reg SHO Restriction Indicator Message indicating the Rule 201 status for NASDAQ-listed securities *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol_long : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (reg_sho_action_value, bytes) =>
                                  Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol_long := symbol_long_value; reg_sho_action := reg_sho_action_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegShoShortSalePriceTestRestrictedIndicatorMessage.

  Module LimitUpLimitDownPriceBandMessage.

    (** LULD Price Band Message containing the Limit Up-Limit Down price bands for a NASDAQ-listed security *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol_long : list byte;
      luld_price_band_indicator : list byte;
      luld_price_band_effective_time : N;
      limit_down_price : N;
      limit_up_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      Datatypes.length (luld_price_band_indicator record) = 1 /\
      (luld_price_band_effective_time record < 256 ^ N.of_nat 8)%N /\
      (limit_down_price record < 256 ^ N.of_nat 8)%N /\
      (limit_up_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_bytes 1 (luld_price_band_indicator record) ++
      encode_uint 8 (luld_price_band_effective_time record) ++
      encode_uint 8 (limit_down_price record) ++
      encode_uint 8 (limit_up_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (luld_price_band_indicator_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (luld_price_band_effective_time_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (limit_down_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (limit_up_price_value, bytes) =>
                                              Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol_long := symbol_long_value; luld_price_band_indicator := luld_price_band_indicator_value; luld_price_band_effective_time := luld_price_band_effective_time_value; limit_down_price := limit_down_price_value; limit_up_price := limit_up_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LimitUpLimitDownPriceBandMessage.

  Module MarketWideCircuitBreakerDeclineLevelMessage.

    (** MWCB Decline Message informing participants and UTP data recipients of the daily MWCB breach points *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      mwcb_level_1 : N;
      mwcb_level_2 : N;
      mwcb_level_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_uint 8 (mwcb_level_1 record) ++
      encode_uint 8 (mwcb_level_2 record) ++
      encode_uint 8 (mwcb_level_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (mwcb_level_1_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (mwcb_level_2_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (mwcb_level_3_value, bytes) =>
                                      Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; mwcb_level_1 := mwcb_level_1_value; mwcb_level_2 := mwcb_level_2_value; mwcb_level_3 := mwcb_level_3_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketWideCircuitBreakerDeclineLevelMessage.

  Module MarketWideCircuitBreakerStatusMessage.

    (** MWCB Status Message informing participants when a MWCB has breached one of the established levels *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      mwcb_status_level_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (mwcb_status_level_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 1 (mwcb_status_level_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (mwcb_status_level_indicator_value, bytes) =>
                              Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; mwcb_status_level_indicator := mwcb_status_level_indicator_value |}, bytes)
                          end
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketWideCircuitBreakerStatusMessage.

  Module AuctionCollarMessage.

    (** Auction Collar Message published by primary markets using an automated reopening to communicate auction collars after a LULD Trading Pause *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
      symbol_long : list byte;
      trading_action_sequence_number : N;
      collar_reference_price : N;
      collar_up_price : N;
      collar_down_price : N;
      collar_extension_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 11 /\
      (trading_action_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (collar_up_price record < 256 ^ N.of_nat 8)%N /\
      (collar_down_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (collar_extension_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record) ++
      encode_bytes 11 (symbol_long record) ++
      encode_uint 4 (trading_action_sequence_number record) ++
      encode_uint 8 (collar_reference_price record) ++
      encode_uint 8 (collar_up_price record) ++
      encode_uint 8 (collar_down_price record) ++
      encode_bytes 1 (collar_extension_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (symbol_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trading_action_sequence_number_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (collar_reference_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (collar_up_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (collar_down_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (collar_extension_indicator_value, bytes) =>
                                                  Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value; symbol_long := symbol_long_value; trading_action_sequence_number := trading_action_sequence_number_value; collar_reference_price := collar_reference_price_value; collar_up_price := collar_up_price_value; collar_down_price := collar_down_price_value; collar_extension_indicator := collar_extension_indicator_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionCollarMessage.

  Module StartOfDayMessage.

    (** Signifies the beginning of each operational cycle for SIP Processing *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StartOfDayMessage.

  Module EndOfDayMessage.

    (** Signals the end of active message dissemination for the UTP SIP operational cycle *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfDayMessage.

  Module MarketSessionOpenMessage.

    (** Signifies the opening of market systems for the session indicated in the Message Header *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSessionOpenMessage.

  Module MarketSessionCloseMessage.

    (** Signals the closing of market systems for the session indicated in the Message Header *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSessionCloseMessage.

  Module EndOfTransmissionsMessage.

    (** Signals that there will be no further transmissions of data sent through the UTP SIP line. Transmitted at the end of the day and will be the last message of the day *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfTransmissionsMessage.

  Module QuoteWipeOutMessage.

    (** Sent to indicate that a UTP Participant is experiencing a problem with their internal systems and is unable to update their UTP BBO quotation information. Disseminated only when a UTP participant is requesting the SIP to remove its quote from ALL NASDAQ-listed securities *)
    Record t := {
      market_center_originator : list byte;
      sub_market_center_id : list byte;
      sip_timestamp : N;
      timestamp_1 : N;
      participant_token : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center_originator record) = 1 /\
      Datatypes.length (sub_market_center_id record) = 1 /\
      (sip_timestamp record < 256 ^ N.of_nat 8)%N /\
      (timestamp_1 record < 256 ^ N.of_nat 8)%N /\
      (participant_token record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center_originator record) ++
      encode_bytes 1 (sub_market_center_id record) ++
      encode_uint 8 (sip_timestamp record) ++
      encode_uint 8 (timestamp_1 record) ++
      encode_uint 8 (participant_token record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_originator_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sub_market_center_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (sip_timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (participant_token_value, bytes) =>
                          Some ({| market_center_originator := market_center_originator_value; sub_market_center_id := sub_market_center_id_value; sip_timestamp := sip_timestamp_value; timestamp_1 := timestamp_1_value; participant_token := participant_token_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteWipeOutMessage.

End NasdaqUqdfOutputV30C.
