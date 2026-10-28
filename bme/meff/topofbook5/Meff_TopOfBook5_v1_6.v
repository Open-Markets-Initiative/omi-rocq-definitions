From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsas y Mercados Españoles MEFF Top Of Book Five Levels

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
      - a run counted by a field
  *)

Module MeffTopOfBook5V16.

  Module MessageHeader.

    (** What every message carries, in either direction: its length and its type. Section 2.1 gives a published message a third field, the sequence number that lets a listener continue an interrupted session without gaps and without repeated messages, and the message tables state it as the message's own first field - which is where it is declared, since a client's Logon, Replay Request and Logout do not carry one *)
    Record t := {
      message_size : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_size := message_size_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module LogonResponseMessage.

    (** The Logon Response message is used by the Server to accept a new session. In this message the sequence number will always be 0 *)
    Record t := {
      sequence_number : N;
      heart_bt_int : N;
      protocol_version : list byte;
      test_production_ind : list byte;
      environment_code : list byte;
      session_date : N;
      expected_sequence_number : N;
      sequence_number_to : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (heart_bt_int record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (protocol_version record) = 6 /\
      Datatypes.length (test_production_ind record) = 1 /\
      Datatypes.length (environment_code record) = 2 /\
      (session_date record < 256 ^ N.of_nat 4)%N /\
      (expected_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (sequence_number_to record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (heart_bt_int record) ++
      encode_bytes 6 (protocol_version record) ++
      encode_bytes 1 (test_production_ind record) ++
      encode_bytes 2 (environment_code record) ++
      encode_uint 4 (session_date record) ++
      encode_uint 4 (expected_sequence_number record) ++
      encode_uint 4 (sequence_number_to record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (heart_bt_int_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (protocol_version_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (test_production_ind_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (environment_code_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (session_date_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (expected_sequence_number_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (sequence_number_to_value, bytes) =>
                                      Some ({| sequence_number := sequence_number_value; heart_bt_int := heart_bt_int_value; protocol_version := protocol_version_value; test_production_ind := test_production_ind_value; environment_code := environment_code_value; session_date := session_date_value; expected_sequence_number := expected_sequence_number_value; sequence_number_to := sequence_number_to_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonResponseMessage.

  Module LogoutResponseMessage.

    (** The Logout message is used by the Server to notify the end of a session, whether it is solicited or unsolicited. It may also be the answer to a failed logon attempt (see Logon message) *)
    Record t := {
      sequence_number : N;
      logout_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (logout_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (logout_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (logout_reason_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; logout_reason := logout_reason_value |}, bytes)
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

  End LogoutResponseMessage.

  Module HeartbeatMessage.

    (** The Heartbeat message is used by the Server to indicate that the communication is active. In the Heartbeat message, the SequenceNumber of the previously received message will be repeated *)
    Record t := {
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          Some ({| sequence_number := sequence_number_value |}, bytes)
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

  End HeartbeatMessage.

  Module NetworkStatusMessage.

    (** Message sent by the server with information about the connectivity between the Server and the central systems. In the Network Status message, the SequenceNumber of the previously received message will be repeated *)
    Record t := {
      sequence_number : N;
      network_status_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (network_status_value record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (network_status_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (network_status_value_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; network_status_value := network_status_value_value |}, bytes)
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

  End NetworkStatusMessage.

  Module TradingSessionStatusMessage.

    (** Sent by the server to inform about the session status in each Trading Mode *)
    Record t := {
      sequence_number : N;
      trading_session_id : N;
      trading_session_sub_id : N;
      trad_ses_status : N;
      transaction_date_and_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trading_session_sub_id record < 256 ^ N.of_nat 1)%N /\
      (trad_ses_status record < 256 ^ N.of_nat 1)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 1 (trading_session_sub_id record) ++
      encode_uint 1 (trad_ses_status record) ++
      encode_uint 8 (transaction_date_and_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (trading_session_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_sub_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trad_ses_status_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (transaction_date_and_time_value, bytes) =>
                          Some ({| sequence_number := sequence_number_value; trading_session_id := trading_session_id_value; trading_session_sub_id := trading_session_sub_id_value; trad_ses_status := trad_ses_status_value; transaction_date_and_time := transaction_date_and_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End TradingSessionStatusMessage.

  Module NewsMessage.

    (** Used by the Server to communicate a Market Surveillance or system-wide text message *)
    Record t := {
      sequence_number : N;
      news_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (news_text record) = 78.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 78 (news_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 78 bytes with
          | None => None
          | Some (news_text_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; news_text := news_text_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 82.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewsMessage.

  Module SecurityListCancellationReportMessage.

    (** Message sent by the server for cancelling previously defined securities *)
    Record t := {
      sequence_number : N;
      market_id : list byte;
      market_segment_id : list byte;
      security_code : N;
      symbol : list byte;
      symbol_isin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_id record) = 4 /\
      Datatypes.length (market_segment_id record) = 4 /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 22 /\
      Datatypes.length (symbol_isin record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 4 (market_id record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 4 (security_code record) ++
      encode_bytes 22 (symbol record) ++
      encode_bytes 12 (symbol_isin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_segment_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (symbol_isin_value, bytes) =>
                              Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityListCancellationReportMessage.

  Module SecurityListMessage.

    (** Message sent by the server to provide the definition of one security. It shares the same layout as the Security List Update Report message, but with a different Message Type *)
    Record t := {
      sequence_number : N;
      market_id : list byte;
      market_segment_id : list byte;
      security_code : N;
      symbol : list byte;
      symbol_isin : list byte;
      fisn : list byte;
      issuer_lei : list byte;
      security_group : list byte;
      family_code : list byte;
      cfi_code : list byte;
      security_type : list byte;
      maturity_date : N;
      issue_date : N;
      contract_multiplier : N;
      li_spre : N;
      sst_ipre : N;
      li_spost : N;
      sst_ipost : N;
      liquid_instrument : N;
      admission_requested_by_issuer : N;
      min_trade_vol : N;
      round_lot : N;
      currency : list byte;
      modality_mask_b_4 : N;
      security_description : list byte;
      trading_obligation : N;
      sec_description : list byte;
      underlying_asset : list byte;
      security_sub_type : list byte;
      maturity_month_year : list byte;
      strike_price : N;
      strike_value : N;
      opt_attribute : list byte;
      min_price_increment : N;
      unit_of_measure : list byte;
      settl_method : list byte;
      exercise_style : list byte;
      put_or_call : list byte;
      flexible_indicator : list byte;
      last_trading_day : N;
      number_of_decimals : N;
      order_number_of_decimals : N;
      adjustments_rule : list byte;
      maximum_order_size : N;
      self_match_prevention : N;
      commodity_derivative_indicator : list byte;
      stock_when_underlying_is_dividend : list byte;
      base_product : list byte;
      sub_product : list byte;
      further_sub_product : list byte;
      base_currency : list byte;
      quoted_currency : list byte;
      maturity_month_year_increment_units : list byte;
      start_maturity_month_year : list byte;
      end_maturity_month_year : list byte;
      maturity_month_year_increment : N;
      underlying_symbol : list byte;
      underlying_isin : list byte;
      underlying_currency : list byte;
      underlying_security_issuer_lei : list byte;
      x_rolling_closing_type : list byte;
      x_rolling_reference_buyer_rate : list byte;
      x_rolling_buyer_markup : N;
      x_rolling_reference_seller_rate : list byte;
      x_rolling_seller_markup : N;
      x_rolling_dividend_percentage : N;
      x_rolling_dividend_pay_date_diff : N;
      leg_symbol_1 : list byte;
      leg_ratio_qty_1 : N;
      leg_side_1 : list byte;
      leg_price_1 : N;
      leg_symbol_2 : list byte;
      leg_ratio_qty_2 : N;
      leg_side_2 : list byte;
      leg_price_2 : N;
      leg_symbol_3 : list byte;
      leg_ratio_qty_3 : N;
      leg_side_3 : list byte;
      leg_price_3 : N;
      leg_symbol_4 : list byte;
      leg_ratio_qty_4 : N;
      leg_side_4 : list byte;
      leg_price_4 : N;
      leg_symbol_5 : list byte;
      leg_ratio_qty_5 : N;
      leg_side_5 : list byte;
      leg_price_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_id record) = 4 /\
      Datatypes.length (market_segment_id record) = 4 /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 22 /\
      Datatypes.length (symbol_isin record) = 12 /\
      Datatypes.length (fisn record) = 35 /\
      Datatypes.length (issuer_lei record) = 20 /\
      Datatypes.length (security_group record) = 2 /\
      Datatypes.length (family_code record) = 5 /\
      Datatypes.length (cfi_code record) = 6 /\
      Datatypes.length (security_type record) = 2 /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (issue_date record < 256 ^ N.of_nat 4)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 8)%N /\
      (li_spre record < 256 ^ N.of_nat 8)%N /\
      (sst_ipre record < 256 ^ N.of_nat 8)%N /\
      (li_spost record < 256 ^ N.of_nat 8)%N /\
      (sst_ipost record < 256 ^ N.of_nat 8)%N /\
      (liquid_instrument record < 256 ^ N.of_nat 1)%N /\
      (admission_requested_by_issuer record < 256 ^ N.of_nat 1)%N /\
      (min_trade_vol record < 256 ^ N.of_nat 4)%N /\
      (round_lot record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 3 /\
      (modality_mask_b_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_description record) = 80 /\
      (trading_obligation record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sec_description record) = 20 /\
      Datatypes.length (underlying_asset record) = 22 /\
      Datatypes.length (security_sub_type record) = 12 /\
      Datatypes.length (maturity_month_year record) = 8 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (strike_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (opt_attribute record) = 1 /\
      (min_price_increment record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (unit_of_measure record) = 20 /\
      Datatypes.length (settl_method record) = 1 /\
      Datatypes.length (exercise_style record) = 1 /\
      Datatypes.length (put_or_call record) = 1 /\
      Datatypes.length (flexible_indicator record) = 1 /\
      (last_trading_day record < 256 ^ N.of_nat 4)%N /\
      (number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (order_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (adjustments_rule record) = 1 /\
      (maximum_order_size record < 256 ^ N.of_nat 8)%N /\
      (self_match_prevention record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (commodity_derivative_indicator record) = 1 /\
      Datatypes.length (stock_when_underlying_is_dividend record) = 22 /\
      Datatypes.length (base_product record) = 4 /\
      Datatypes.length (sub_product record) = 4 /\
      Datatypes.length (further_sub_product record) = 4 /\
      Datatypes.length (base_currency record) = 3 /\
      Datatypes.length (quoted_currency record) = 3 /\
      Datatypes.length (maturity_month_year_increment_units record) = 1 /\
      Datatypes.length (start_maturity_month_year record) = 8 /\
      Datatypes.length (end_maturity_month_year record) = 8 /\
      (maturity_month_year_increment record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 22 /\
      Datatypes.length (underlying_isin record) = 12 /\
      Datatypes.length (underlying_currency record) = 3 /\
      Datatypes.length (underlying_security_issuer_lei record) = 20 /\
      Datatypes.length (x_rolling_closing_type record) = 1 /\
      Datatypes.length (x_rolling_reference_buyer_rate record) = 1 /\
      (x_rolling_buyer_markup record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (x_rolling_reference_seller_rate record) = 1 /\
      (x_rolling_seller_markup record < 256 ^ N.of_nat 8)%N /\
      (x_rolling_dividend_percentage record < 256 ^ N.of_nat 8)%N /\
      (x_rolling_dividend_pay_date_diff record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (leg_symbol_1 record) = 22 /\
      (leg_ratio_qty_1 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_1 record) = 1 /\
      (leg_price_1 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_symbol_2 record) = 22 /\
      (leg_ratio_qty_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_2 record) = 1 /\
      (leg_price_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_symbol_3 record) = 22 /\
      (leg_ratio_qty_3 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_3 record) = 1 /\
      (leg_price_3 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_symbol_4 record) = 22 /\
      (leg_ratio_qty_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_4 record) = 1 /\
      (leg_price_4 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_symbol_5 record) = 22 /\
      (leg_ratio_qty_5 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_5 record) = 1 /\
      (leg_price_5 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 4 (market_id record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 4 (security_code record) ++
      encode_bytes 22 (symbol record) ++
      encode_bytes 12 (symbol_isin record) ++
      encode_bytes 35 (fisn record) ++
      encode_bytes 20 (issuer_lei record) ++
      encode_bytes 2 (security_group record) ++
      encode_bytes 5 (family_code record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_bytes 2 (security_type record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 4 (issue_date record) ++
      encode_uint 8 (contract_multiplier record) ++
      encode_uint 8 (li_spre record) ++
      encode_uint 8 (sst_ipre record) ++
      encode_uint 8 (li_spost record) ++
      encode_uint 8 (sst_ipost record) ++
      encode_uint 1 (liquid_instrument record) ++
      encode_uint 1 (admission_requested_by_issuer record) ++
      encode_uint 4 (min_trade_vol record) ++
      encode_uint 4 (round_lot record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 4 (modality_mask_b_4 record) ++
      encode_bytes 80 (security_description record) ++
      encode_uint 1 (trading_obligation record) ++
      encode_bytes 20 (sec_description record) ++
      encode_bytes 22 (underlying_asset record) ++
      encode_bytes 12 (security_sub_type record) ++
      encode_bytes 8 (maturity_month_year record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 8 (strike_value record) ++
      encode_bytes 1 (opt_attribute record) ++
      encode_uint 8 (min_price_increment record) ++
      encode_bytes 20 (unit_of_measure record) ++
      encode_bytes 1 (settl_method record) ++
      encode_bytes 1 (exercise_style record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_bytes 1 (flexible_indicator record) ++
      encode_uint 4 (last_trading_day record) ++
      encode_uint 1 (number_of_decimals record) ++
      encode_uint 1 (order_number_of_decimals record) ++
      encode_bytes 1 (adjustments_rule record) ++
      encode_uint 8 (maximum_order_size record) ++
      encode_uint 1 (self_match_prevention record) ++
      encode_bytes 1 (commodity_derivative_indicator record) ++
      encode_bytes 22 (stock_when_underlying_is_dividend record) ++
      encode_bytes 4 (base_product record) ++
      encode_bytes 4 (sub_product record) ++
      encode_bytes 4 (further_sub_product record) ++
      encode_bytes 3 (base_currency record) ++
      encode_bytes 3 (quoted_currency record) ++
      encode_bytes 1 (maturity_month_year_increment_units record) ++
      encode_bytes 8 (start_maturity_month_year record) ++
      encode_bytes 8 (end_maturity_month_year record) ++
      encode_uint 1 (maturity_month_year_increment record) ++
      encode_bytes 22 (underlying_symbol record) ++
      encode_bytes 12 (underlying_isin record) ++
      encode_bytes 3 (underlying_currency record) ++
      encode_bytes 20 (underlying_security_issuer_lei record) ++
      encode_bytes 1 (x_rolling_closing_type record) ++
      encode_bytes 1 (x_rolling_reference_buyer_rate record) ++
      encode_uint 8 (x_rolling_buyer_markup record) ++
      encode_bytes 1 (x_rolling_reference_seller_rate record) ++
      encode_uint 8 (x_rolling_seller_markup record) ++
      encode_uint 8 (x_rolling_dividend_percentage record) ++
      encode_uint 2 (x_rolling_dividend_pay_date_diff record) ++
      encode_bytes 22 (leg_symbol_1 record) ++
      encode_uint 4 (leg_ratio_qty_1 record) ++
      encode_bytes 1 (leg_side_1 record) ++
      encode_uint 8 (leg_price_1 record) ++
      encode_bytes 22 (leg_symbol_2 record) ++
      encode_uint 4 (leg_ratio_qty_2 record) ++
      encode_bytes 1 (leg_side_2 record) ++
      encode_uint 8 (leg_price_2 record) ++
      encode_bytes 22 (leg_symbol_3 record) ++
      encode_uint 4 (leg_ratio_qty_3 record) ++
      encode_bytes 1 (leg_side_3 record) ++
      encode_uint 8 (leg_price_3 record) ++
      encode_bytes 22 (leg_symbol_4 record) ++
      encode_uint 4 (leg_ratio_qty_4 record) ++
      encode_bytes 1 (leg_side_4 record) ++
      encode_uint 8 (leg_price_4 record) ++
      encode_bytes 22 (leg_symbol_5 record) ++
      encode_uint 4 (leg_ratio_qty_5 record) ++
      encode_bytes 1 (leg_side_5 record) ++
      encode_uint 8 (leg_price_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_segment_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (symbol_isin_value, bytes) =>
                              match decode_bytes 35 bytes with
                              | None => None
                              | Some (fisn_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (issuer_lei_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (security_group_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (family_code_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (cfi_code_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (security_type_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (maturity_date_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (issue_date_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (contract_multiplier_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (li_spre_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (sst_ipre_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (li_spost_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (sst_ipost_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (liquid_instrument_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (admission_requested_by_issuer_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (min_trade_vol_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (round_lot_value, bytes) =>
                                                                                                  match decode_bytes 3 bytes with
                                                                                                  | None => None
                                                                                                  | Some (currency_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (modality_mask_b_4_value, bytes) =>
                                                                                                          match decode_bytes 80 bytes with
                                                                                                          | None => None
                                                                                                          | Some (security_description_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (trading_obligation_value, bytes) =>
                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (sec_description_value, bytes) =>
                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (underlying_asset_value, bytes) =>
                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (security_sub_type_value, bytes) =>
                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (maturity_month_year_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (strike_price_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (strike_value_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (opt_attribute_value, bytes) =>
                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (min_price_increment_value, bytes) =>
                                                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (unit_of_measure_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (settl_method_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (exercise_style_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (put_or_call_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (flexible_indicator_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (last_trading_day_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (number_of_decimals_value, bytes) =>
                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (order_number_of_decimals_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (adjustments_rule_value, bytes) =>
                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (maximum_order_size_value, bytes) =>
                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (self_match_prevention_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (commodity_derivative_indicator_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (stock_when_underlying_is_dividend_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (base_product_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (sub_product_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (further_sub_product_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (base_currency_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (quoted_currency_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (maturity_month_year_increment_units_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (start_maturity_month_year_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (end_maturity_month_year_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (maturity_month_year_increment_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (underlying_symbol_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (underlying_isin_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (underlying_currency_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (underlying_security_issuer_lei_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (x_rolling_closing_type_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (x_rolling_reference_buyer_rate_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (x_rolling_buyer_markup_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (x_rolling_reference_seller_rate_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (x_rolling_seller_markup_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (x_rolling_dividend_percentage_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (x_rolling_dividend_pay_date_diff_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (leg_symbol_1_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_1_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (leg_side_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (leg_price_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (leg_symbol_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (leg_side_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (leg_price_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (leg_symbol_3_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_3_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (leg_side_3_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (leg_price_3_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (leg_symbol_4_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_4_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (leg_side_4_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (leg_price_4_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (leg_symbol_5_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_5_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (leg_side_5_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (leg_price_5_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value; fisn := fisn_value; issuer_lei := issuer_lei_value; security_group := security_group_value; family_code := family_code_value; cfi_code := cfi_code_value; security_type := security_type_value; maturity_date := maturity_date_value; issue_date := issue_date_value; contract_multiplier := contract_multiplier_value; li_spre := li_spre_value; sst_ipre := sst_ipre_value; li_spost := li_spost_value; sst_ipost := sst_ipost_value; liquid_instrument := liquid_instrument_value; admission_requested_by_issuer := admission_requested_by_issuer_value; min_trade_vol := min_trade_vol_value; round_lot := round_lot_value; currency := currency_value; modality_mask_b_4 := modality_mask_b_4_value; security_description := security_description_value; trading_obligation := trading_obligation_value; sec_description := sec_description_value; underlying_asset := underlying_asset_value; security_sub_type := security_sub_type_value; maturity_month_year := maturity_month_year_value; strike_price := strike_price_value; strike_value := strike_value_value; opt_attribute := opt_attribute_value; min_price_increment := min_price_increment_value; unit_of_measure := unit_of_measure_value; settl_method := settl_method_value; exercise_style := exercise_style_value; put_or_call := put_or_call_value; flexible_indicator := flexible_indicator_value; last_trading_day := last_trading_day_value; number_of_decimals := number_of_decimals_value; order_number_of_decimals := order_number_of_decimals_value; adjustments_rule := adjustments_rule_value; maximum_order_size := maximum_order_size_value; self_match_prevention := self_match_prevention_value; commodity_derivative_indicator := commodity_derivative_indicator_value; stock_when_underlying_is_dividend := stock_when_underlying_is_dividend_value; base_product := base_product_value; sub_product := sub_product_value; further_sub_product := further_sub_product_value; base_currency := base_currency_value; quoted_currency := quoted_currency_value; maturity_month_year_increment_units := maturity_month_year_increment_units_value; start_maturity_month_year := start_maturity_month_year_value; end_maturity_month_year := end_maturity_month_year_value; maturity_month_year_increment := maturity_month_year_increment_value; underlying_symbol := underlying_symbol_value; underlying_isin := underlying_isin_value; underlying_currency := underlying_currency_value; underlying_security_issuer_lei := underlying_security_issuer_lei_value; x_rolling_closing_type := x_rolling_closing_type_value; x_rolling_reference_buyer_rate := x_rolling_reference_buyer_rate_value; x_rolling_buyer_markup := x_rolling_buyer_markup_value; x_rolling_reference_seller_rate := x_rolling_reference_seller_rate_value; x_rolling_seller_markup := x_rolling_seller_markup_value; x_rolling_dividend_percentage := x_rolling_dividend_percentage_value; x_rolling_dividend_pay_date_diff := x_rolling_dividend_pay_date_diff_value; leg_symbol_1 := leg_symbol_1_value; leg_ratio_qty_1 := leg_ratio_qty_1_value; leg_side_1 := leg_side_1_value; leg_price_1 := leg_price_1_value; leg_symbol_2 := leg_symbol_2_value; leg_ratio_qty_2 := leg_ratio_qty_2_value; leg_side_2 := leg_side_2_value; leg_price_2 := leg_price_2_value; leg_symbol_3 := leg_symbol_3_value; leg_ratio_qty_3 := leg_ratio_qty_3_value; leg_side_3 := leg_side_3_value; leg_price_3 := leg_price_3_value; leg_symbol_4 := leg_symbol_4_value; leg_ratio_qty_4 := leg_ratio_qty_4_value; leg_side_4 := leg_side_4_value; leg_price_4 := leg_price_4_value; leg_symbol_5 := leg_symbol_5_value; leg_ratio_qty_5 := leg_ratio_qty_5_value; leg_side_5 := leg_side_5_value; leg_price_5 := leg_price_5_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 713.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 bound_87]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
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
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_bytes by exact bound_46.
      rewrite decode_encode_bytes by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_bytes by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_bytes by exact bound_54.
      rewrite decode_encode_bytes by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_uint by exact bound_65.
      rewrite decode_encode_uint by exact bound_66.
      rewrite decode_encode_uint by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      rewrite decode_encode_uint by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      rewrite decode_encode_uint by exact bound_75.
      rewrite decode_encode_bytes by exact bound_76.
      rewrite decode_encode_uint by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_uint by exact bound_79.
      rewrite decode_encode_bytes by exact bound_80.
      rewrite decode_encode_uint by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_uint by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_uint by exact bound_85.
      rewrite decode_encode_bytes by exact bound_86.
      rewrite decode_encode_uint by exact bound_87.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityListMessage.

  Module SecurityListUpdateReportMessage.

    (** Message sent by the server for reporting updates, during the session, to the security definition *)
    Record t := {
      sequence_number : N;
      market_id : list byte;
      market_segment_id : list byte;
      security_code : N;
      symbol : list byte;
      symbol_isin : list byte;
      fisn : list byte;
      issuer_lei : list byte;
      security_group : list byte;
      family_code : list byte;
      cfi_code : list byte;
      security_type : list byte;
      maturity_date : N;
      issue_date : N;
      contract_multiplier : N;
      li_spre : N;
      sst_ipre : N;
      li_spost : N;
      sst_ipost : N;
      liquid_instrument : N;
      admission_requested_by_issuer : N;
      min_trade_vol : N;
      round_lot : N;
      currency : list byte;
      modality_mask_b_4 : N;
      security_description : list byte;
      trading_obligation : N;
      sec_description : list byte;
      underlying_asset : list byte;
      security_sub_type : list byte;
      maturity_month_year : list byte;
      strike_price : N;
      strike_value : N;
      opt_attribute : list byte;
      min_price_increment : N;
      unit_of_measure : list byte;
      settl_method : list byte;
      exercise_style : list byte;
      put_or_call : list byte;
      flexible_indicator : list byte;
      last_trading_day : N;
      number_of_decimals : N;
      order_number_of_decimals : N;
      adjustments_rule : list byte;
      maximum_order_size : N;
      self_match_prevention : N;
      commodity_derivative_indicator : list byte;
      stock_when_underlying_is_dividend : list byte;
      base_product : list byte;
      sub_product : list byte;
      further_sub_product : list byte;
      base_currency : list byte;
      quoted_currency : list byte;
      maturity_month_year_increment_units : list byte;
      start_maturity_month_year : list byte;
      end_maturity_month_year : list byte;
      maturity_month_year_increment : N;
      underlying_symbol : list byte;
      underlying_isin : list byte;
      underlying_currency : list byte;
      underlying_security_issuer_lei : list byte;
      x_rolling_closing_type : list byte;
      x_rolling_reference_buyer_rate : list byte;
      x_rolling_buyer_markup : N;
      x_rolling_reference_seller_rate : list byte;
      x_rolling_seller_markup : N;
      x_rolling_dividend_percentage : N;
      x_rolling_dividend_pay_date_diff : N;
      leg_symbol_1 : list byte;
      leg_ratio_qty_1 : N;
      leg_side_1 : list byte;
      leg_price_1 : N;
      leg_symbol_2 : list byte;
      leg_ratio_qty_2 : N;
      leg_side_2 : list byte;
      leg_price_2 : N;
      leg_symbol_3 : list byte;
      leg_ratio_qty_3 : N;
      leg_side_3 : list byte;
      leg_price_3 : N;
      leg_symbol_4 : list byte;
      leg_ratio_qty_4 : N;
      leg_side_4 : list byte;
      leg_price_4 : N;
      leg_symbol_5 : list byte;
      leg_ratio_qty_5 : N;
      leg_side_5 : list byte;
      leg_price_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_id record) = 4 /\
      Datatypes.length (market_segment_id record) = 4 /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 22 /\
      Datatypes.length (symbol_isin record) = 12 /\
      Datatypes.length (fisn record) = 35 /\
      Datatypes.length (issuer_lei record) = 20 /\
      Datatypes.length (security_group record) = 2 /\
      Datatypes.length (family_code record) = 5 /\
      Datatypes.length (cfi_code record) = 6 /\
      Datatypes.length (security_type record) = 2 /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      (issue_date record < 256 ^ N.of_nat 4)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 8)%N /\
      (li_spre record < 256 ^ N.of_nat 8)%N /\
      (sst_ipre record < 256 ^ N.of_nat 8)%N /\
      (li_spost record < 256 ^ N.of_nat 8)%N /\
      (sst_ipost record < 256 ^ N.of_nat 8)%N /\
      (liquid_instrument record < 256 ^ N.of_nat 1)%N /\
      (admission_requested_by_issuer record < 256 ^ N.of_nat 1)%N /\
      (min_trade_vol record < 256 ^ N.of_nat 4)%N /\
      (round_lot record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 3 /\
      (modality_mask_b_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_description record) = 80 /\
      (trading_obligation record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sec_description record) = 20 /\
      Datatypes.length (underlying_asset record) = 22 /\
      Datatypes.length (security_sub_type record) = 12 /\
      Datatypes.length (maturity_month_year record) = 8 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (strike_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (opt_attribute record) = 1 /\
      (min_price_increment record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (unit_of_measure record) = 20 /\
      Datatypes.length (settl_method record) = 1 /\
      Datatypes.length (exercise_style record) = 1 /\
      Datatypes.length (put_or_call record) = 1 /\
      Datatypes.length (flexible_indicator record) = 1 /\
      (last_trading_day record < 256 ^ N.of_nat 4)%N /\
      (number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (order_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (adjustments_rule record) = 1 /\
      (maximum_order_size record < 256 ^ N.of_nat 8)%N /\
      (self_match_prevention record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (commodity_derivative_indicator record) = 1 /\
      Datatypes.length (stock_when_underlying_is_dividend record) = 22 /\
      Datatypes.length (base_product record) = 4 /\
      Datatypes.length (sub_product record) = 4 /\
      Datatypes.length (further_sub_product record) = 4 /\
      Datatypes.length (base_currency record) = 3 /\
      Datatypes.length (quoted_currency record) = 3 /\
      Datatypes.length (maturity_month_year_increment_units record) = 1 /\
      Datatypes.length (start_maturity_month_year record) = 8 /\
      Datatypes.length (end_maturity_month_year record) = 8 /\
      (maturity_month_year_increment record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 22 /\
      Datatypes.length (underlying_isin record) = 12 /\
      Datatypes.length (underlying_currency record) = 3 /\
      Datatypes.length (underlying_security_issuer_lei record) = 20 /\
      Datatypes.length (x_rolling_closing_type record) = 1 /\
      Datatypes.length (x_rolling_reference_buyer_rate record) = 1 /\
      (x_rolling_buyer_markup record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (x_rolling_reference_seller_rate record) = 1 /\
      (x_rolling_seller_markup record < 256 ^ N.of_nat 8)%N /\
      (x_rolling_dividend_percentage record < 256 ^ N.of_nat 8)%N /\
      (x_rolling_dividend_pay_date_diff record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (leg_symbol_1 record) = 22 /\
      (leg_ratio_qty_1 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_1 record) = 1 /\
      (leg_price_1 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_symbol_2 record) = 22 /\
      (leg_ratio_qty_2 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_2 record) = 1 /\
      (leg_price_2 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_symbol_3 record) = 22 /\
      (leg_ratio_qty_3 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_3 record) = 1 /\
      (leg_price_3 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_symbol_4 record) = 22 /\
      (leg_ratio_qty_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_4 record) = 1 /\
      (leg_price_4 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_symbol_5 record) = 22 /\
      (leg_ratio_qty_5 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side_5 record) = 1 /\
      (leg_price_5 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 4 (market_id record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 4 (security_code record) ++
      encode_bytes 22 (symbol record) ++
      encode_bytes 12 (symbol_isin record) ++
      encode_bytes 35 (fisn record) ++
      encode_bytes 20 (issuer_lei record) ++
      encode_bytes 2 (security_group record) ++
      encode_bytes 5 (family_code record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_bytes 2 (security_type record) ++
      encode_uint 4 (maturity_date record) ++
      encode_uint 4 (issue_date record) ++
      encode_uint 8 (contract_multiplier record) ++
      encode_uint 8 (li_spre record) ++
      encode_uint 8 (sst_ipre record) ++
      encode_uint 8 (li_spost record) ++
      encode_uint 8 (sst_ipost record) ++
      encode_uint 1 (liquid_instrument record) ++
      encode_uint 1 (admission_requested_by_issuer record) ++
      encode_uint 4 (min_trade_vol record) ++
      encode_uint 4 (round_lot record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 4 (modality_mask_b_4 record) ++
      encode_bytes 80 (security_description record) ++
      encode_uint 1 (trading_obligation record) ++
      encode_bytes 20 (sec_description record) ++
      encode_bytes 22 (underlying_asset record) ++
      encode_bytes 12 (security_sub_type record) ++
      encode_bytes 8 (maturity_month_year record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 8 (strike_value record) ++
      encode_bytes 1 (opt_attribute record) ++
      encode_uint 8 (min_price_increment record) ++
      encode_bytes 20 (unit_of_measure record) ++
      encode_bytes 1 (settl_method record) ++
      encode_bytes 1 (exercise_style record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_bytes 1 (flexible_indicator record) ++
      encode_uint 4 (last_trading_day record) ++
      encode_uint 1 (number_of_decimals record) ++
      encode_uint 1 (order_number_of_decimals record) ++
      encode_bytes 1 (adjustments_rule record) ++
      encode_uint 8 (maximum_order_size record) ++
      encode_uint 1 (self_match_prevention record) ++
      encode_bytes 1 (commodity_derivative_indicator record) ++
      encode_bytes 22 (stock_when_underlying_is_dividend record) ++
      encode_bytes 4 (base_product record) ++
      encode_bytes 4 (sub_product record) ++
      encode_bytes 4 (further_sub_product record) ++
      encode_bytes 3 (base_currency record) ++
      encode_bytes 3 (quoted_currency record) ++
      encode_bytes 1 (maturity_month_year_increment_units record) ++
      encode_bytes 8 (start_maturity_month_year record) ++
      encode_bytes 8 (end_maturity_month_year record) ++
      encode_uint 1 (maturity_month_year_increment record) ++
      encode_bytes 22 (underlying_symbol record) ++
      encode_bytes 12 (underlying_isin record) ++
      encode_bytes 3 (underlying_currency record) ++
      encode_bytes 20 (underlying_security_issuer_lei record) ++
      encode_bytes 1 (x_rolling_closing_type record) ++
      encode_bytes 1 (x_rolling_reference_buyer_rate record) ++
      encode_uint 8 (x_rolling_buyer_markup record) ++
      encode_bytes 1 (x_rolling_reference_seller_rate record) ++
      encode_uint 8 (x_rolling_seller_markup record) ++
      encode_uint 8 (x_rolling_dividend_percentage record) ++
      encode_uint 2 (x_rolling_dividend_pay_date_diff record) ++
      encode_bytes 22 (leg_symbol_1 record) ++
      encode_uint 4 (leg_ratio_qty_1 record) ++
      encode_bytes 1 (leg_side_1 record) ++
      encode_uint 8 (leg_price_1 record) ++
      encode_bytes 22 (leg_symbol_2 record) ++
      encode_uint 4 (leg_ratio_qty_2 record) ++
      encode_bytes 1 (leg_side_2 record) ++
      encode_uint 8 (leg_price_2 record) ++
      encode_bytes 22 (leg_symbol_3 record) ++
      encode_uint 4 (leg_ratio_qty_3 record) ++
      encode_bytes 1 (leg_side_3 record) ++
      encode_uint 8 (leg_price_3 record) ++
      encode_bytes 22 (leg_symbol_4 record) ++
      encode_uint 4 (leg_ratio_qty_4 record) ++
      encode_bytes 1 (leg_side_4 record) ++
      encode_uint 8 (leg_price_4 record) ++
      encode_bytes 22 (leg_symbol_5 record) ++
      encode_uint 4 (leg_ratio_qty_5 record) ++
      encode_bytes 1 (leg_side_5 record) ++
      encode_uint 8 (leg_price_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (market_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (market_segment_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (symbol_isin_value, bytes) =>
                              match decode_bytes 35 bytes with
                              | None => None
                              | Some (fisn_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (issuer_lei_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (security_group_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (family_code_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (cfi_code_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (security_type_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (maturity_date_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (issue_date_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (contract_multiplier_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (li_spre_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (sst_ipre_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (li_spost_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (sst_ipost_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (liquid_instrument_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (admission_requested_by_issuer_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (min_trade_vol_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (round_lot_value, bytes) =>
                                                                                                  match decode_bytes 3 bytes with
                                                                                                  | None => None
                                                                                                  | Some (currency_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (modality_mask_b_4_value, bytes) =>
                                                                                                          match decode_bytes 80 bytes with
                                                                                                          | None => None
                                                                                                          | Some (security_description_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (trading_obligation_value, bytes) =>
                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (sec_description_value, bytes) =>
                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (underlying_asset_value, bytes) =>
                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (security_sub_type_value, bytes) =>
                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (maturity_month_year_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (strike_price_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (strike_value_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (opt_attribute_value, bytes) =>
                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (min_price_increment_value, bytes) =>
                                                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (unit_of_measure_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (settl_method_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (exercise_style_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (put_or_call_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (flexible_indicator_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (last_trading_day_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (number_of_decimals_value, bytes) =>
                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (order_number_of_decimals_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (adjustments_rule_value, bytes) =>
                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (maximum_order_size_value, bytes) =>
                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (self_match_prevention_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (commodity_derivative_indicator_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (stock_when_underlying_is_dividend_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (base_product_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (sub_product_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (further_sub_product_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (base_currency_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (quoted_currency_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (maturity_month_year_increment_units_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (start_maturity_month_year_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (end_maturity_month_year_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (maturity_month_year_increment_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (underlying_symbol_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (underlying_isin_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (underlying_currency_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (underlying_security_issuer_lei_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (x_rolling_closing_type_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (x_rolling_reference_buyer_rate_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (x_rolling_buyer_markup_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (x_rolling_reference_seller_rate_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (x_rolling_seller_markup_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (x_rolling_dividend_percentage_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (x_rolling_dividend_pay_date_diff_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (leg_symbol_1_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_1_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (leg_side_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (leg_price_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (leg_symbol_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (leg_side_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (leg_price_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (leg_symbol_3_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_3_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (leg_side_3_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (leg_price_3_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (leg_symbol_4_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_4_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (leg_side_4_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (leg_price_4_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (leg_symbol_5_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (leg_ratio_qty_5_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (leg_side_5_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (leg_price_5_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value; fisn := fisn_value; issuer_lei := issuer_lei_value; security_group := security_group_value; family_code := family_code_value; cfi_code := cfi_code_value; security_type := security_type_value; maturity_date := maturity_date_value; issue_date := issue_date_value; contract_multiplier := contract_multiplier_value; li_spre := li_spre_value; sst_ipre := sst_ipre_value; li_spost := li_spost_value; sst_ipost := sst_ipost_value; liquid_instrument := liquid_instrument_value; admission_requested_by_issuer := admission_requested_by_issuer_value; min_trade_vol := min_trade_vol_value; round_lot := round_lot_value; currency := currency_value; modality_mask_b_4 := modality_mask_b_4_value; security_description := security_description_value; trading_obligation := trading_obligation_value; sec_description := sec_description_value; underlying_asset := underlying_asset_value; security_sub_type := security_sub_type_value; maturity_month_year := maturity_month_year_value; strike_price := strike_price_value; strike_value := strike_value_value; opt_attribute := opt_attribute_value; min_price_increment := min_price_increment_value; unit_of_measure := unit_of_measure_value; settl_method := settl_method_value; exercise_style := exercise_style_value; put_or_call := put_or_call_value; flexible_indicator := flexible_indicator_value; last_trading_day := last_trading_day_value; number_of_decimals := number_of_decimals_value; order_number_of_decimals := order_number_of_decimals_value; adjustments_rule := adjustments_rule_value; maximum_order_size := maximum_order_size_value; self_match_prevention := self_match_prevention_value; commodity_derivative_indicator := commodity_derivative_indicator_value; stock_when_underlying_is_dividend := stock_when_underlying_is_dividend_value; base_product := base_product_value; sub_product := sub_product_value; further_sub_product := further_sub_product_value; base_currency := base_currency_value; quoted_currency := quoted_currency_value; maturity_month_year_increment_units := maturity_month_year_increment_units_value; start_maturity_month_year := start_maturity_month_year_value; end_maturity_month_year := end_maturity_month_year_value; maturity_month_year_increment := maturity_month_year_increment_value; underlying_symbol := underlying_symbol_value; underlying_isin := underlying_isin_value; underlying_currency := underlying_currency_value; underlying_security_issuer_lei := underlying_security_issuer_lei_value; x_rolling_closing_type := x_rolling_closing_type_value; x_rolling_reference_buyer_rate := x_rolling_reference_buyer_rate_value; x_rolling_buyer_markup := x_rolling_buyer_markup_value; x_rolling_reference_seller_rate := x_rolling_reference_seller_rate_value; x_rolling_seller_markup := x_rolling_seller_markup_value; x_rolling_dividend_percentage := x_rolling_dividend_percentage_value; x_rolling_dividend_pay_date_diff := x_rolling_dividend_pay_date_diff_value; leg_symbol_1 := leg_symbol_1_value; leg_ratio_qty_1 := leg_ratio_qty_1_value; leg_side_1 := leg_side_1_value; leg_price_1 := leg_price_1_value; leg_symbol_2 := leg_symbol_2_value; leg_ratio_qty_2 := leg_ratio_qty_2_value; leg_side_2 := leg_side_2_value; leg_price_2 := leg_price_2_value; leg_symbol_3 := leg_symbol_3_value; leg_ratio_qty_3 := leg_ratio_qty_3_value; leg_side_3 := leg_side_3_value; leg_price_3 := leg_price_3_value; leg_symbol_4 := leg_symbol_4_value; leg_ratio_qty_4 := leg_ratio_qty_4_value; leg_side_4 := leg_side_4_value; leg_price_4 := leg_price_4_value; leg_symbol_5 := leg_symbol_5_value; leg_ratio_qty_5 := leg_ratio_qty_5_value; leg_side_5 := leg_side_5_value; leg_price_5 := leg_price_5_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 713.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 bound_87]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
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
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_bytes by exact bound_46.
      rewrite decode_encode_bytes by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_bytes by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_bytes by exact bound_54.
      rewrite decode_encode_bytes by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_uint by exact bound_65.
      rewrite decode_encode_uint by exact bound_66.
      rewrite decode_encode_uint by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      rewrite decode_encode_uint by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      rewrite decode_encode_uint by exact bound_75.
      rewrite decode_encode_bytes by exact bound_76.
      rewrite decode_encode_uint by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_uint by exact bound_79.
      rewrite decode_encode_bytes by exact bound_80.
      rewrite decode_encode_uint by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_uint by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_uint by exact bound_85.
      rewrite decode_encode_bytes by exact bound_86.
      rewrite decode_encode_uint by exact bound_87.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityListUpdateReportMessage.

  Module SecurityStatusMessage.

    (** Message sent by the server to inform on the status of one security *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      security_trading_status : N;
      non_availability_reason : N;
      high_limit_price : N;
      low_limit_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (non_availability_reason record < 256 ^ N.of_nat 1)%N /\
      (high_limit_price record < 256 ^ N.of_nat 8)%N /\
      (low_limit_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 1 (non_availability_reason record) ++
      encode_uint 8 (high_limit_price record) ++
      encode_uint 8 (low_limit_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (security_trading_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (non_availability_reason_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (high_limit_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (low_limit_price_value, bytes) =>
                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; security_trading_status := security_trading_status_value; non_availability_reason := non_availability_reason_value; high_limit_price := high_limit_price_value; low_limit_price := low_limit_price_value |}, bytes)
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

  End SecurityStatusMessage.

  Module FamilyStatusMessage.

    (** Message sent by the server in the Derivatives environment to inform about the status a Family of products *)
    Record t := {
      sequence_number : N;
      security_group : list byte;
      family_code : list byte;
      transaction_date_and_time : N;
      security_trading_status : N;
      non_availability_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_group record) = 2 /\
      Datatypes.length (family_code record) = 5 /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (non_availability_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_bytes 2 (security_group record) ++
      encode_bytes 5 (family_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 1 (non_availability_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (security_group_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (family_code_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transaction_date_and_time_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (security_trading_status_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (non_availability_reason_value, bytes) =>
                              Some ({| sequence_number := sequence_number_value; security_group := security_group_value; family_code := family_code_value; transaction_date_and_time := transaction_date_and_time_value; security_trading_status := security_trading_status_value; non_availability_reason := non_availability_reason_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FamilyStatusMessage.

  Module TradeMarketPostTransparencyInformationTopOfBookMessage.

    (** Used by the server to communicate trade information related to trades resulting from order matching in channels C/D and E/F. It is also used in channels A/B when the trade is the result of order matching at the end of an auction period (where only top-of-book information is shown) *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      market_segment_id : list byte;
      trading_session_id : N;
      trd_match_id : N;
      trade_type : list byte;
      last_px : N;
      last_qty : N;
      gross_trade_amt : N;
      designation : list byte;
      market_mechanism : list byte;
      algo_flag : N;
      transaction_category : list byte;
      strategy_trd_match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_segment_id record) = 4 /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trd_match_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (gross_trade_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (designation record) = 1 /\
      Datatypes.length (market_mechanism record) = 1 /\
      (algo_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (strategy_trd_match_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 4 (trd_match_id record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (gross_trade_amt record) ++
      encode_bytes 1 (designation record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_uint 1 (algo_flag record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 4 (strategy_trd_match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trading_session_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trd_match_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (gross_trade_amt_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (designation_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (market_mechanism_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (algo_flag_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (transaction_category_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (strategy_trd_match_id_value, bytes) =>
                                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; transaction_category := transaction_category_value; strategy_trd_match_id := strategy_trd_match_id_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMarketPostTransparencyInformationTopOfBookMessage.

  Module TradeTradeAmendmentOrCancellationMessage.

    (** Sent by the server to inform about a trade produced due to any reason other than order matching, also to inform about trades produced due to order matching in a Dark pool. In this message, all fields with the suffix 2 refer to the sell order, and the ones without the suffix refer either to both legs or the buy order *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      market_segment_id : list byte;
      trading_session_id : N;
      trd_match_id : N;
      trade_type : list byte;
      last_px : N;
      last_qty : N;
      gross_trade_amt : N;
      designation : list byte;
      market_mechanism : list byte;
      algo_flag : N;
      transaction_category : list byte;
      strategy_trd_match_id : N;
      last_change_flag : N;
      benc_rfpt_flag : list byte;
      trade_price_condition : list byte;
      pre_trade_transparency_waiver : list byte;
      deferral_waiver : list byte;
      post_deferral_publication_type : list byte;
      publish_date_and_time : N;
      trade_date : N;
      trade_session_date : N;
      amended_trade_type : list byte;
      exec_ref_id : N;
      amended_trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_segment_id record) = 4 /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (trd_match_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (last_px record < 256 ^ N.of_nat 8)%N /\
      (last_qty record < 256 ^ N.of_nat 4)%N /\
      (gross_trade_amt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (designation record) = 1 /\
      Datatypes.length (market_mechanism record) = 1 /\
      (algo_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (strategy_trd_match_id record < 256 ^ N.of_nat 4)%N /\
      (last_change_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (benc_rfpt_flag record) = 1 /\
      Datatypes.length (trade_price_condition record) = 1 /\
      Datatypes.length (pre_trade_transparency_waiver record) = 1 /\
      Datatypes.length (deferral_waiver record) = 1 /\
      Datatypes.length (post_deferral_publication_type record) = 1 /\
      (publish_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (trade_session_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (amended_trade_type record) = 1 /\
      (exec_ref_id record < 256 ^ N.of_nat 4)%N /\
      (amended_trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_bytes 4 (market_segment_id record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 4 (trd_match_id record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (last_px record) ++
      encode_uint 4 (last_qty record) ++
      encode_uint 8 (gross_trade_amt record) ++
      encode_bytes 1 (designation record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_uint 1 (algo_flag record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 4 (strategy_trd_match_id record) ++
      encode_uint 1 (last_change_flag record) ++
      encode_bytes 1 (benc_rfpt_flag record) ++
      encode_bytes 1 (trade_price_condition record) ++
      encode_bytes 1 (pre_trade_transparency_waiver record) ++
      encode_bytes 1 (deferral_waiver record) ++
      encode_bytes 1 (post_deferral_publication_type record) ++
      encode_uint 8 (publish_date_and_time record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 4 (trade_session_date record) ++
      encode_bytes 1 (amended_trade_type record) ++
      encode_uint 4 (exec_ref_id record) ++
      encode_uint 4 (amended_trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_segment_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trading_session_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trd_match_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_px_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (last_qty_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (gross_trade_amt_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (designation_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (market_mechanism_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (algo_flag_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (transaction_category_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (strategy_trd_match_id_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (last_change_flag_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (benc_rfpt_flag_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (trade_price_condition_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (pre_trade_transparency_waiver_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (deferral_waiver_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (post_deferral_publication_type_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (publish_date_and_time_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (trade_date_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trade_session_date_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (amended_trade_type_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (exec_ref_id_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (amended_trade_date_value, bytes) =>
                                                                                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; transaction_category := transaction_category_value; strategy_trd_match_id := strategy_trd_match_id_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; post_deferral_publication_type := post_deferral_publication_type_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value |}, bytes)
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeTradeAmendmentOrCancellationMessage.

  Module IndicationOfInterestMessage.

    (** Used by the Server to notify an indication of interest on a specific instrument. This functionality is available in Fixed Income and Derivatives *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      ioiid : N;
      ioi_trans_type : list byte;
      side : list byte;
      ioi_qty : N;
      ioi_price : N;
      ioi_qlty_ind : list byte;
      trading_session_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (ioiid record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ioi_trans_type record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (ioi_qty record < 256 ^ N.of_nat 4)%N /\
      (ioi_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ioi_qlty_ind record) = 1 /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 4 (ioiid record) ++
      encode_bytes 1 (ioi_trans_type record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (ioi_qty record) ++
      encode_uint 8 (ioi_price record) ++
      encode_bytes 1 (ioi_qlty_ind record) ++
      encode_uint 1 (trading_session_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ioiid_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (ioi_trans_type_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (ioi_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (ioi_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (ioi_qlty_ind_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trading_session_id_value, bytes) =>
                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; ioiid := ioiid_value; ioi_trans_type := ioi_trans_type_value; side := side_value; ioi_qty := ioi_qty_value; ioi_price := ioi_price_value; ioi_qlty_ind := ioi_qlty_ind_value; trading_session_id := trading_session_id_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndicationOfInterestMessage.

  Module RfqMarketPreTransparencyInformationMessage.

    (** Used by the server to communicate price information about RFQs. The contents of the RFQID field match those of the field IOIID in the corresponding Indication of Interest message *)
    Record t := {
      sequence_number : N;
      rfqid : N;
      trading_session_id : N;
      security_code : N;
      transaction_date_and_time : N;
      mid_buy_price : N;
      mid_buy_volume : N;
      buy_rf_qs_number : N;
      mid_sell_price : N;
      mid_sell_volume : N;
      sell_rf_qs_number : N;
      bid_orders_1 : N;
      bid_size_1 : N;
      bid_px_1 : N;
      ask_orders_1 : N;
      ask_size_1 : N;
      ask_px_1 : N;
      bid_orders_2 : N;
      bid_size_2 : N;
      bid_px_2 : N;
      ask_orders_2 : N;
      ask_size_2 : N;
      ask_px_2 : N;
      bid_orders_3 : N;
      bid_size_3 : N;
      bid_px_3 : N;
      ask_orders_3 : N;
      ask_size_3 : N;
      ask_px_3 : N;
      bid_orders_4 : N;
      bid_size_4 : N;
      bid_px_4 : N;
      ask_orders_4 : N;
      ask_size_4 : N;
      ask_px_4 : N;
      bid_orders_5 : N;
      bid_size_5 : N;
      bid_px_5 : N;
      ask_orders_5 : N;
      ask_size_5 : N;
      ask_px_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (rfqid record < 256 ^ N.of_nat 4)%N /\
      (trading_session_id record < 256 ^ N.of_nat 1)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (mid_buy_price record < 256 ^ N.of_nat 8)%N /\
      (mid_buy_volume record < 256 ^ N.of_nat 4)%N /\
      (buy_rf_qs_number record < 256 ^ N.of_nat 2)%N /\
      (mid_sell_price record < 256 ^ N.of_nat 8)%N /\
      (mid_sell_volume record < 256 ^ N.of_nat 4)%N /\
      (sell_rf_qs_number record < 256 ^ N.of_nat 2)%N /\
      (bid_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_1 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_1 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_1 record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_2 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_2 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_2 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_2 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_2 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_2 record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_3 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_3 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_3 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_3 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_3 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_3 record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_4 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_4 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_4 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_4 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_4 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_4 record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_5 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_5 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_5 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_5 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_5 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_5 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (rfqid record) ++
      encode_uint 1 (trading_session_id record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 8 (mid_buy_price record) ++
      encode_uint 4 (mid_buy_volume record) ++
      encode_uint 2 (buy_rf_qs_number record) ++
      encode_uint 8 (mid_sell_price record) ++
      encode_uint 4 (mid_sell_volume record) ++
      encode_uint 2 (sell_rf_qs_number record) ++
      encode_uint 2 (bid_orders_1 record) ++
      encode_uint 4 (bid_size_1 record) ++
      encode_uint 8 (bid_px_1 record) ++
      encode_uint 2 (ask_orders_1 record) ++
      encode_uint 4 (ask_size_1 record) ++
      encode_uint 8 (ask_px_1 record) ++
      encode_uint 2 (bid_orders_2 record) ++
      encode_uint 4 (bid_size_2 record) ++
      encode_uint 8 (bid_px_2 record) ++
      encode_uint 2 (ask_orders_2 record) ++
      encode_uint 4 (ask_size_2 record) ++
      encode_uint 8 (ask_px_2 record) ++
      encode_uint 2 (bid_orders_3 record) ++
      encode_uint 4 (bid_size_3 record) ++
      encode_uint 8 (bid_px_3 record) ++
      encode_uint 2 (ask_orders_3 record) ++
      encode_uint 4 (ask_size_3 record) ++
      encode_uint 8 (ask_px_3 record) ++
      encode_uint 2 (bid_orders_4 record) ++
      encode_uint 4 (bid_size_4 record) ++
      encode_uint 8 (bid_px_4 record) ++
      encode_uint 2 (ask_orders_4 record) ++
      encode_uint 4 (ask_size_4 record) ++
      encode_uint 8 (ask_px_4 record) ++
      encode_uint 2 (bid_orders_5 record) ++
      encode_uint 4 (bid_size_5 record) ++
      encode_uint 8 (bid_px_5 record) ++
      encode_uint 2 (ask_orders_5 record) ++
      encode_uint 4 (ask_size_5 record) ++
      encode_uint 8 (ask_px_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (rfqid_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (transaction_date_and_time_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (mid_buy_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (mid_buy_volume_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (buy_rf_qs_number_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (mid_sell_price_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (mid_sell_volume_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (sell_rf_qs_number_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (bid_orders_1_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (bid_size_1_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (bid_px_1_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (ask_orders_1_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (ask_size_1_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (ask_px_1_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (bid_orders_2_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (bid_size_2_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_px_2_value, bytes) =>
                                                                                      match decode_uint 2 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_orders_2_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_size_2_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_px_2_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_orders_3_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_size_3_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_px_3_value, bytes) =>
                                                                                                              match decode_uint 2 bytes with
                                                                                                              | None => None
                                                                                                              | Some (ask_orders_3_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_size_3_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_px_3_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_orders_4_value, bytes) =>
                                                                                                                              match decode_uint 4 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_size_4_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_px_4_value, bytes) =>
                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_orders_4_value, bytes) =>
                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_size_4_value, bytes) =>
                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_px_4_value, bytes) =>
                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_orders_5_value, bytes) =>
                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_size_5_value, bytes) =>
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_px_5_value, bytes) =>
                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ask_orders_5_value, bytes) =>
                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_size_5_value, bytes) =>
                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_px_5_value, bytes) =>
                                                                                                                                                                          Some ({| sequence_number := sequence_number_value; rfqid := rfqid_value; trading_session_id := trading_session_id_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; mid_buy_price := mid_buy_price_value; mid_buy_volume := mid_buy_volume_value; buy_rf_qs_number := buy_rf_qs_number_value; mid_sell_price := mid_sell_price_value; mid_sell_volume := mid_sell_volume_value; sell_rf_qs_number := sell_rf_qs_number_value; bid_orders_1 := bid_orders_1_value; bid_size_1 := bid_size_1_value; bid_px_1 := bid_px_1_value; ask_orders_1 := ask_orders_1_value; ask_size_1 := ask_size_1_value; ask_px_1 := ask_px_1_value; bid_orders_2 := bid_orders_2_value; bid_size_2 := bid_size_2_value; bid_px_2 := bid_px_2_value; ask_orders_2 := ask_orders_2_value; ask_size_2 := ask_size_2_value; ask_px_2 := ask_px_2_value; bid_orders_3 := bid_orders_3_value; bid_size_3 := bid_size_3_value; bid_px_3 := bid_px_3_value; ask_orders_3 := ask_orders_3_value; ask_size_3 := ask_size_3_value; ask_px_3 := ask_px_3_value; bid_orders_4 := bid_orders_4_value; bid_size_4 := bid_size_4_value; bid_px_4 := bid_px_4_value; ask_orders_4 := ask_orders_4_value; ask_size_4 := ask_size_4_value; ask_px_4 := ask_px_4_value; bid_orders_5 := bid_orders_5_value; bid_size_5 := bid_size_5_value; bid_px_5 := bid_px_5_value; ask_orders_5 := ask_orders_5_value; ask_size_5 := ask_size_5_value; ask_px_5 := ask_px_5_value |}, bytes)
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 189.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 bound_40]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RfqMarketPreTransparencyInformationMessage.

  Module TopOfBookMessage.

    (** Used by the UDP Servers to communicate Top-of-book price information during auctions. When there is an indicative match price, the fields BidPx1 and AskPx1 will have the same value *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      bid_orders_1 : N;
      bid_size_1 : N;
      bid_px_1 : N;
      retail_cl_bid_flag_1 : N;
      ask_orders_1 : N;
      ask_size_1 : N;
      ask_px_1 : N;
      retail_cl_ask_flag_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_1 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_bid_flag_1 record < 256 ^ N.of_nat 1)%N /\
      (ask_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_1 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_1 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_ask_flag_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 2 (bid_orders_1 record) ++
      encode_uint 4 (bid_size_1 record) ++
      encode_uint 8 (bid_px_1 record) ++
      encode_uint 1 (retail_cl_bid_flag_1 record) ++
      encode_uint 2 (ask_orders_1 record) ++
      encode_uint 4 (ask_size_1 record) ++
      encode_uint 8 (ask_px_1 record) ++
      encode_uint 1 (retail_cl_ask_flag_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_orders_1_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_size_1_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_px_1_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (retail_cl_bid_flag_1_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (ask_orders_1_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (ask_size_1_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (ask_px_1_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (retail_cl_ask_flag_1_value, bytes) =>
                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; bid_orders_1 := bid_orders_1_value; bid_size_1 := bid_size_1_value; bid_px_1 := bid_px_1_value; retail_cl_bid_flag_1 := retail_cl_bid_flag_1_value; ask_orders_1 := ask_orders_1_value; ask_size_1 := ask_size_1_value; ask_px_1 := ask_px_1_value; retail_cl_ask_flag_1 := retail_cl_ask_flag_1_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TopOfBookMessage.

  Module TopOfBook5LevelsMessage.

    (** Used by the UDP 5 level top-of-book Servers to communicate Top-of-book price information during open market. During auctions, only the first level is shown, and therefore this message is not published, and the message Top-of-book (Msg Type = 0x82) is used instead *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      bid_orders_1 : N;
      bid_size_1 : N;
      bid_px_1 : N;
      retail_cl_bid_flag_1 : N;
      ask_orders_1 : N;
      ask_size_1 : N;
      ask_px_1 : N;
      retail_cl_ask_flag_1 : N;
      bid_orders_2 : N;
      bid_size_2 : N;
      bid_px_2 : N;
      retail_cl_bid_flag_2 : N;
      ask_orders_2 : N;
      ask_size_2 : N;
      ask_px_2 : N;
      retail_cl_ask_flag_2 : N;
      bid_orders_3 : N;
      bid_size_3 : N;
      bid_px_3 : N;
      retail_cl_bid_flag_3 : N;
      ask_orders_3 : N;
      ask_size_3 : N;
      ask_px_3 : N;
      retail_cl_ask_flag_3 : N;
      bid_orders_4 : N;
      bid_size_4 : N;
      bid_px_4 : N;
      retail_cl_bid_flag_4 : N;
      ask_orders_4 : N;
      ask_size_4 : N;
      ask_px_4 : N;
      retail_cl_ask_flag_4 : N;
      bid_orders_5 : N;
      bid_size_5 : N;
      bid_px_5 : N;
      retail_cl_bid_flag_5 : N;
      ask_orders_5 : N;
      ask_size_5 : N;
      ask_px_5 : N;
      retail_cl_ask_flag_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_1 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_bid_flag_1 record < 256 ^ N.of_nat 1)%N /\
      (ask_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_1 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_1 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_ask_flag_1 record < 256 ^ N.of_nat 1)%N /\
      (bid_orders_2 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_2 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_2 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_bid_flag_2 record < 256 ^ N.of_nat 1)%N /\
      (ask_orders_2 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_2 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_2 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_ask_flag_2 record < 256 ^ N.of_nat 1)%N /\
      (bid_orders_3 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_3 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_3 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_bid_flag_3 record < 256 ^ N.of_nat 1)%N /\
      (ask_orders_3 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_3 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_3 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_ask_flag_3 record < 256 ^ N.of_nat 1)%N /\
      (bid_orders_4 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_4 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_4 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_bid_flag_4 record < 256 ^ N.of_nat 1)%N /\
      (ask_orders_4 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_4 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_4 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_ask_flag_4 record < 256 ^ N.of_nat 1)%N /\
      (bid_orders_5 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_5 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_5 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_bid_flag_5 record < 256 ^ N.of_nat 1)%N /\
      (ask_orders_5 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_5 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_5 record < 256 ^ N.of_nat 8)%N /\
      (retail_cl_ask_flag_5 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 2 (bid_orders_1 record) ++
      encode_uint 4 (bid_size_1 record) ++
      encode_uint 8 (bid_px_1 record) ++
      encode_uint 1 (retail_cl_bid_flag_1 record) ++
      encode_uint 2 (ask_orders_1 record) ++
      encode_uint 4 (ask_size_1 record) ++
      encode_uint 8 (ask_px_1 record) ++
      encode_uint 1 (retail_cl_ask_flag_1 record) ++
      encode_uint 2 (bid_orders_2 record) ++
      encode_uint 4 (bid_size_2 record) ++
      encode_uint 8 (bid_px_2 record) ++
      encode_uint 1 (retail_cl_bid_flag_2 record) ++
      encode_uint 2 (ask_orders_2 record) ++
      encode_uint 4 (ask_size_2 record) ++
      encode_uint 8 (ask_px_2 record) ++
      encode_uint 1 (retail_cl_ask_flag_2 record) ++
      encode_uint 2 (bid_orders_3 record) ++
      encode_uint 4 (bid_size_3 record) ++
      encode_uint 8 (bid_px_3 record) ++
      encode_uint 1 (retail_cl_bid_flag_3 record) ++
      encode_uint 2 (ask_orders_3 record) ++
      encode_uint 4 (ask_size_3 record) ++
      encode_uint 8 (ask_px_3 record) ++
      encode_uint 1 (retail_cl_ask_flag_3 record) ++
      encode_uint 2 (bid_orders_4 record) ++
      encode_uint 4 (bid_size_4 record) ++
      encode_uint 8 (bid_px_4 record) ++
      encode_uint 1 (retail_cl_bid_flag_4 record) ++
      encode_uint 2 (ask_orders_4 record) ++
      encode_uint 4 (ask_size_4 record) ++
      encode_uint 8 (ask_px_4 record) ++
      encode_uint 1 (retail_cl_ask_flag_4 record) ++
      encode_uint 2 (bid_orders_5 record) ++
      encode_uint 4 (bid_size_5 record) ++
      encode_uint 8 (bid_px_5 record) ++
      encode_uint 1 (retail_cl_bid_flag_5 record) ++
      encode_uint 2 (ask_orders_5 record) ++
      encode_uint 4 (ask_size_5 record) ++
      encode_uint 8 (ask_px_5 record) ++
      encode_uint 1 (retail_cl_ask_flag_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_code_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (transaction_date_and_time_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (bid_orders_1_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_size_1_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_px_1_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (retail_cl_bid_flag_1_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (ask_orders_1_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (ask_size_1_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (ask_px_1_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (retail_cl_ask_flag_1_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (bid_orders_2_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (bid_size_2_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (bid_px_2_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (retail_cl_bid_flag_2_value, bytes) =>
                                                                  match decode_uint 2 bytes with
                                                                  | None => None
                                                                  | Some (ask_orders_2_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (ask_size_2_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (ask_px_2_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (retail_cl_ask_flag_2_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_orders_3_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_size_3_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_px_3_value, bytes) =>
                                                                                              match decode_uint 1 bytes with
                                                                                              | None => None
                                                                                              | Some (retail_cl_bid_flag_3_value, bytes) =>
                                                                                                  match decode_uint 2 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_orders_3_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_size_3_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_px_3_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (retail_cl_ask_flag_3_value, bytes) =>
                                                                                                                  match decode_uint 2 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (bid_orders_4_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_size_4_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_px_4_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (retail_cl_bid_flag_4_value, bytes) =>
                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_orders_4_value, bytes) =>
                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_size_4_value, bytes) =>
                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_px_4_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (retail_cl_ask_flag_4_value, bytes) =>
                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_orders_5_value, bytes) =>
                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_size_5_value, bytes) =>
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_px_5_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (retail_cl_bid_flag_5_value, bytes) =>
                                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_orders_5_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_size_5_value, bytes) =>
                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_px_5_value, bytes) =>
                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (retail_cl_ask_flag_5_value, bytes) =>
                                                                                                                                                                                  Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; bid_orders_1 := bid_orders_1_value; bid_size_1 := bid_size_1_value; bid_px_1 := bid_px_1_value; retail_cl_bid_flag_1 := retail_cl_bid_flag_1_value; ask_orders_1 := ask_orders_1_value; ask_size_1 := ask_size_1_value; ask_px_1 := ask_px_1_value; retail_cl_ask_flag_1 := retail_cl_ask_flag_1_value; bid_orders_2 := bid_orders_2_value; bid_size_2 := bid_size_2_value; bid_px_2 := bid_px_2_value; retail_cl_bid_flag_2 := retail_cl_bid_flag_2_value; ask_orders_2 := ask_orders_2_value; ask_size_2 := ask_size_2_value; ask_px_2 := ask_px_2_value; retail_cl_ask_flag_2 := retail_cl_ask_flag_2_value; bid_orders_3 := bid_orders_3_value; bid_size_3 := bid_size_3_value; bid_px_3 := bid_px_3_value; retail_cl_bid_flag_3 := retail_cl_bid_flag_3_value; ask_orders_3 := ask_orders_3_value; ask_size_3 := ask_size_3_value; ask_px_3 := ask_px_3_value; retail_cl_ask_flag_3 := retail_cl_ask_flag_3_value; bid_orders_4 := bid_orders_4_value; bid_size_4 := bid_size_4_value; bid_px_4 := bid_px_4_value; retail_cl_bid_flag_4 := retail_cl_bid_flag_4_value; ask_orders_4 := ask_orders_4_value; ask_size_4 := ask_size_4_value; ask_px_4 := ask_px_4_value; retail_cl_ask_flag_4 := retail_cl_ask_flag_4_value; bid_orders_5 := bid_orders_5_value; bid_size_5 := bid_size_5_value; bid_px_5 := bid_px_5_value; retail_cl_bid_flag_5 := retail_cl_bid_flag_5_value; ask_orders_5 := ask_orders_5_value; ask_size_5 := ask_size_5_value; ask_px_5 := ask_px_5_value; retail_cl_ask_flag_5 := retail_cl_ask_flag_5_value |}, bytes)
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 166.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 bound_42]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TopOfBook5LevelsMessage.

End MeffTopOfBook5V16.
