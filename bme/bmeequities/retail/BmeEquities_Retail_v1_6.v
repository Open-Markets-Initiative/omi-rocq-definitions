From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsas y Mercados Españoles BME Equities Retail Top Of Book

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

Module BmeEquitiesRetailV16.

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
      security_name : list byte;
      net_asset_value_identifier : list byte;
      security_sub_type : list byte;
      maturity_month_year : list byte;
      security_status : list byte;
      strike_price : N;
      strike_value : N;
      exercise_style : list byte;
      put_or_call : list byte;
      position_limit : N;
      nt_position_limit : N;
      issuer : list byte;
      cp_reg_type : N;
      barrier : N;
      last_trading_day : N;
      automatic_expiration : N;
      fee_type : list byte;
      barrier_2 : N;
      trigger_barrier : N;
      trigger_upper_barrier : N;
      average_quarterly_turnover : N;
      trading_scope : N;
      sicav_counterparty_member : list byte;
      net_asset_value_indicator : N;
      reference_trading_venue : list byte;
      outstanding_capital : N;
      first_trading_date : N;
      settlement_system : list byte;
      number_of_decimals : N;
      number_of_holders : N;
      outstanding_shares : N;
      minimum_authorized_shares : N;
      minimum_capital : N;
      last_admission_date : N;
      barrier_return : N;
      investment_fund_manager : list byte;
      effective_amount_filters_routed_orders : N;
      order_number_of_decimals : N;
      investment_fund_class : N;
      master_fund_name : list byte;
      investment_fund_management_company : list byte;
      investment_fund_depository : list byte;
      investment_fund_category : list byte;
      investment_fund_minimum_subscription_amount : N;
      investment_fund_minimum_maintenance_amount : N;
      investment_fund_cut_off_time : N;
      nav_communication_term : list byte;
      investment_fund_number_of_decimals : N;
      commodity_derivative_indicator : list byte;
      double_volume_cap_reached : N;
      adt : N;
      base_product : list byte;
      sub_product : list byte;
      further_sub_product : list byte;
      adnt : N;
      price_tick_rule : N;
      underlying_symbol : list byte;
      underlying_isin : list byte;
      underlying_currency : list byte;
      minimum_display_qty : N;
      retail_service_flag : N;
      self_match_prevention : N;
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
      Datatypes.length (security_name record) = 40 /\
      Datatypes.length (net_asset_value_identifier record) = 7 /\
      Datatypes.length (security_sub_type record) = 2 /\
      Datatypes.length (maturity_month_year record) = 8 /\
      Datatypes.length (security_status record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (strike_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exercise_style record) = 1 /\
      Datatypes.length (put_or_call record) = 1 /\
      (position_limit record < 256 ^ N.of_nat 8)%N /\
      (nt_position_limit record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issuer record) = 12 /\
      (cp_reg_type record < 256 ^ N.of_nat 1)%N /\
      (barrier record < 256 ^ N.of_nat 8)%N /\
      (last_trading_day record < 256 ^ N.of_nat 4)%N /\
      (automatic_expiration record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (fee_type record) = 2 /\
      (barrier_2 record < 256 ^ N.of_nat 8)%N /\
      (trigger_barrier record < 256 ^ N.of_nat 8)%N /\
      (trigger_upper_barrier record < 256 ^ N.of_nat 8)%N /\
      (average_quarterly_turnover record < 256 ^ N.of_nat 8)%N /\
      (trading_scope record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sicav_counterparty_member record) = 4 /\
      (net_asset_value_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference_trading_venue record) = 1 /\
      (outstanding_capital record < 256 ^ N.of_nat 8)%N /\
      (first_trading_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_system record) = 1 /\
      (number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (number_of_holders record < 256 ^ N.of_nat 4)%N /\
      (outstanding_shares record < 256 ^ N.of_nat 4)%N /\
      (minimum_authorized_shares record < 256 ^ N.of_nat 4)%N /\
      (minimum_capital record < 256 ^ N.of_nat 8)%N /\
      (last_admission_date record < 256 ^ N.of_nat 4)%N /\
      (barrier_return record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (investment_fund_manager record) = 80 /\
      (effective_amount_filters_routed_orders record < 256 ^ N.of_nat 8)%N /\
      (order_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (investment_fund_class record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (master_fund_name record) = 80 /\
      Datatypes.length (investment_fund_management_company record) = 80 /\
      Datatypes.length (investment_fund_depository record) = 80 /\
      Datatypes.length (investment_fund_category record) = 80 /\
      (investment_fund_minimum_subscription_amount record < 256 ^ N.of_nat 8)%N /\
      (investment_fund_minimum_maintenance_amount record < 256 ^ N.of_nat 8)%N /\
      (investment_fund_cut_off_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (nav_communication_term record) = 1 /\
      (investment_fund_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (commodity_derivative_indicator record) = 1 /\
      (double_volume_cap_reached record < 256 ^ N.of_nat 1)%N /\
      (adt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_product record) = 4 /\
      Datatypes.length (sub_product record) = 4 /\
      Datatypes.length (further_sub_product record) = 4 /\
      (adnt record < 256 ^ N.of_nat 8)%N /\
      (price_tick_rule record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 22 /\
      Datatypes.length (underlying_isin record) = 12 /\
      Datatypes.length (underlying_currency record) = 3 /\
      (minimum_display_qty record < 256 ^ N.of_nat 4)%N /\
      (retail_service_flag record < 256 ^ N.of_nat 1)%N /\
      (self_match_prevention record < 256 ^ N.of_nat 1)%N.

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
      encode_bytes 40 (security_name record) ++
      encode_bytes 7 (net_asset_value_identifier record) ++
      encode_bytes 2 (security_sub_type record) ++
      encode_bytes 8 (maturity_month_year record) ++
      encode_bytes 1 (security_status record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 8 (strike_value record) ++
      encode_bytes 1 (exercise_style record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_uint 8 (position_limit record) ++
      encode_uint 8 (nt_position_limit record) ++
      encode_bytes 12 (issuer record) ++
      encode_uint 1 (cp_reg_type record) ++
      encode_uint 8 (barrier record) ++
      encode_uint 4 (last_trading_day record) ++
      encode_uint 1 (automatic_expiration record) ++
      encode_bytes 2 (fee_type record) ++
      encode_uint 8 (barrier_2 record) ++
      encode_uint 8 (trigger_barrier record) ++
      encode_uint 8 (trigger_upper_barrier record) ++
      encode_uint 8 (average_quarterly_turnover record) ++
      encode_uint 1 (trading_scope record) ++
      encode_bytes 4 (sicav_counterparty_member record) ++
      encode_uint 1 (net_asset_value_indicator record) ++
      encode_bytes 1 (reference_trading_venue record) ++
      encode_uint 8 (outstanding_capital record) ++
      encode_uint 4 (first_trading_date record) ++
      encode_bytes 1 (settlement_system record) ++
      encode_uint 1 (number_of_decimals record) ++
      encode_uint 4 (number_of_holders record) ++
      encode_uint 4 (outstanding_shares record) ++
      encode_uint 4 (minimum_authorized_shares record) ++
      encode_uint 8 (minimum_capital record) ++
      encode_uint 4 (last_admission_date record) ++
      encode_uint 8 (barrier_return record) ++
      encode_bytes 80 (investment_fund_manager record) ++
      encode_uint 8 (effective_amount_filters_routed_orders record) ++
      encode_uint 1 (order_number_of_decimals record) ++
      encode_uint 1 (investment_fund_class record) ++
      encode_bytes 80 (master_fund_name record) ++
      encode_bytes 80 (investment_fund_management_company record) ++
      encode_bytes 80 (investment_fund_depository record) ++
      encode_bytes 80 (investment_fund_category record) ++
      encode_uint 8 (investment_fund_minimum_subscription_amount record) ++
      encode_uint 8 (investment_fund_minimum_maintenance_amount record) ++
      encode_uint 8 (investment_fund_cut_off_time record) ++
      encode_bytes 1 (nav_communication_term record) ++
      encode_uint 1 (investment_fund_number_of_decimals record) ++
      encode_bytes 1 (commodity_derivative_indicator record) ++
      encode_uint 1 (double_volume_cap_reached record) ++
      encode_uint 8 (adt record) ++
      encode_bytes 4 (base_product record) ++
      encode_bytes 4 (sub_product record) ++
      encode_bytes 4 (further_sub_product record) ++
      encode_uint 8 (adnt record) ++
      encode_uint 1 (price_tick_rule record) ++
      encode_bytes 22 (underlying_symbol record) ++
      encode_bytes 12 (underlying_isin record) ++
      encode_bytes 3 (underlying_currency record) ++
      encode_uint 4 (minimum_display_qty record) ++
      encode_uint 1 (retail_service_flag record) ++
      encode_uint 1 (self_match_prevention record).

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
                                                                                                              match decode_bytes 40 bytes with
                                                                                                              | None => None
                                                                                                              | Some (security_name_value, bytes) =>
                                                                                                                  match decode_bytes 7 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (net_asset_value_identifier_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (security_sub_type_value, bytes) =>
                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (maturity_month_year_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (security_status_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (strike_price_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (strike_value_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (exercise_style_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (put_or_call_value, bytes) =>
                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (position_limit_value, bytes) =>
                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (nt_position_limit_value, bytes) =>
                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (issuer_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (cp_reg_type_value, bytes) =>
                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (barrier_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (last_trading_day_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (automatic_expiration_value, bytes) =>
                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (fee_type_value, bytes) =>
                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (barrier_2_value, bytes) =>
                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (trigger_barrier_value, bytes) =>
                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (trigger_upper_barrier_value, bytes) =>
                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (average_quarterly_turnover_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (trading_scope_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (sicav_counterparty_member_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (net_asset_value_indicator_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (reference_trading_venue_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (outstanding_capital_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (first_trading_date_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (settlement_system_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (number_of_holders_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (outstanding_shares_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (minimum_authorized_shares_value, bytes) =>
                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (minimum_capital_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (last_admission_date_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (barrier_return_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (investment_fund_manager_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (effective_amount_filters_routed_orders_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (order_number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (investment_fund_class_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (master_fund_name_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (investment_fund_management_company_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (investment_fund_depository_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (investment_fund_category_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (investment_fund_minimum_subscription_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (investment_fund_minimum_maintenance_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (investment_fund_cut_off_time_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (nav_communication_term_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (investment_fund_number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (commodity_derivative_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (double_volume_cap_reached_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (adt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (base_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (sub_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (further_sub_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (adnt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (price_tick_rule_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (underlying_symbol_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (underlying_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (underlying_currency_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (minimum_display_qty_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (retail_service_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (self_match_prevention_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value; fisn := fisn_value; issuer_lei := issuer_lei_value; security_group := security_group_value; cfi_code := cfi_code_value; security_type := security_type_value; maturity_date := maturity_date_value; issue_date := issue_date_value; contract_multiplier := contract_multiplier_value; li_spre := li_spre_value; sst_ipre := sst_ipre_value; li_spost := li_spost_value; sst_ipost := sst_ipost_value; liquid_instrument := liquid_instrument_value; admission_requested_by_issuer := admission_requested_by_issuer_value; min_trade_vol := min_trade_vol_value; round_lot := round_lot_value; currency := currency_value; modality_mask_b_4 := modality_mask_b_4_value; security_description := security_description_value; trading_obligation := trading_obligation_value; security_name := security_name_value; net_asset_value_identifier := net_asset_value_identifier_value; security_sub_type := security_sub_type_value; maturity_month_year := maturity_month_year_value; security_status := security_status_value; strike_price := strike_price_value; strike_value := strike_value_value; exercise_style := exercise_style_value; put_or_call := put_or_call_value; position_limit := position_limit_value; nt_position_limit := nt_position_limit_value; issuer := issuer_value; cp_reg_type := cp_reg_type_value; barrier := barrier_value; last_trading_day := last_trading_day_value; automatic_expiration := automatic_expiration_value; fee_type := fee_type_value; barrier_2 := barrier_2_value; trigger_barrier := trigger_barrier_value; trigger_upper_barrier := trigger_upper_barrier_value; average_quarterly_turnover := average_quarterly_turnover_value; trading_scope := trading_scope_value; sicav_counterparty_member := sicav_counterparty_member_value; net_asset_value_indicator := net_asset_value_indicator_value; reference_trading_venue := reference_trading_venue_value; outstanding_capital := outstanding_capital_value; first_trading_date := first_trading_date_value; settlement_system := settlement_system_value; number_of_decimals := number_of_decimals_value; number_of_holders := number_of_holders_value; outstanding_shares := outstanding_shares_value; minimum_authorized_shares := minimum_authorized_shares_value; minimum_capital := minimum_capital_value; last_admission_date := last_admission_date_value; barrier_return := barrier_return_value; investment_fund_manager := investment_fund_manager_value; effective_amount_filters_routed_orders := effective_amount_filters_routed_orders_value; order_number_of_decimals := order_number_of_decimals_value; investment_fund_class := investment_fund_class_value; master_fund_name := master_fund_name_value; investment_fund_management_company := investment_fund_management_company_value; investment_fund_depository := investment_fund_depository_value; investment_fund_category := investment_fund_category_value; investment_fund_minimum_subscription_amount := investment_fund_minimum_subscription_amount_value; investment_fund_minimum_maintenance_amount := investment_fund_minimum_maintenance_amount_value; investment_fund_cut_off_time := investment_fund_cut_off_time_value; nav_communication_term := nav_communication_term_value; investment_fund_number_of_decimals := investment_fund_number_of_decimals_value; commodity_derivative_indicator := commodity_derivative_indicator_value; double_volume_cap_reached := double_volume_cap_reached_value; adt := adt_value; base_product := base_product_value; sub_product := sub_product_value; further_sub_product := further_sub_product_value; adnt := adnt_value; price_tick_rule := price_tick_rule_value; underlying_symbol := underlying_symbol_value; underlying_isin := underlying_isin_value; underlying_currency := underlying_currency_value; minimum_display_qty := minimum_display_qty_value; retail_service_flag := retail_service_flag_value; self_match_prevention := self_match_prevention_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 976.
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
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_uint by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_uint by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      rewrite decode_encode_uint by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_uint by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_uint by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_uint by exact bound_70.
      rewrite decode_encode_uint by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      rewrite decode_encode_uint by exact bound_75.
      rewrite decode_encode_uint by exact bound_76.
      rewrite decode_encode_bytes by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_uint by exact bound_80.
      rewrite decode_encode_uint by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_bytes by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_uint by exact bound_85.
      rewrite decode_encode_uint by exact bound_86.
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
      security_name : list byte;
      net_asset_value_identifier : list byte;
      security_sub_type : list byte;
      maturity_month_year : list byte;
      security_status : list byte;
      strike_price : N;
      strike_value : N;
      exercise_style : list byte;
      put_or_call : list byte;
      position_limit : N;
      nt_position_limit : N;
      issuer : list byte;
      cp_reg_type : N;
      barrier : N;
      last_trading_day : N;
      automatic_expiration : N;
      fee_type : list byte;
      barrier_2 : N;
      trigger_barrier : N;
      trigger_upper_barrier : N;
      average_quarterly_turnover : N;
      trading_scope : N;
      sicav_counterparty_member : list byte;
      net_asset_value_indicator : N;
      reference_trading_venue : list byte;
      outstanding_capital : N;
      first_trading_date : N;
      settlement_system : list byte;
      number_of_decimals : N;
      number_of_holders : N;
      outstanding_shares : N;
      minimum_authorized_shares : N;
      minimum_capital : N;
      last_admission_date : N;
      barrier_return : N;
      investment_fund_manager : list byte;
      effective_amount_filters_routed_orders : N;
      order_number_of_decimals : N;
      investment_fund_class : N;
      master_fund_name : list byte;
      investment_fund_management_company : list byte;
      investment_fund_depository : list byte;
      investment_fund_category : list byte;
      investment_fund_minimum_subscription_amount : N;
      investment_fund_minimum_maintenance_amount : N;
      investment_fund_cut_off_time : N;
      nav_communication_term : list byte;
      investment_fund_number_of_decimals : N;
      commodity_derivative_indicator : list byte;
      double_volume_cap_reached : N;
      adt : N;
      base_product : list byte;
      sub_product : list byte;
      further_sub_product : list byte;
      adnt : N;
      price_tick_rule : N;
      underlying_symbol : list byte;
      underlying_isin : list byte;
      underlying_currency : list byte;
      minimum_display_qty : N;
      retail_service_flag : N;
      self_match_prevention : N;
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
      Datatypes.length (security_name record) = 40 /\
      Datatypes.length (net_asset_value_identifier record) = 7 /\
      Datatypes.length (security_sub_type record) = 2 /\
      Datatypes.length (maturity_month_year record) = 8 /\
      Datatypes.length (security_status record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (strike_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exercise_style record) = 1 /\
      Datatypes.length (put_or_call record) = 1 /\
      (position_limit record < 256 ^ N.of_nat 8)%N /\
      (nt_position_limit record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issuer record) = 12 /\
      (cp_reg_type record < 256 ^ N.of_nat 1)%N /\
      (barrier record < 256 ^ N.of_nat 8)%N /\
      (last_trading_day record < 256 ^ N.of_nat 4)%N /\
      (automatic_expiration record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (fee_type record) = 2 /\
      (barrier_2 record < 256 ^ N.of_nat 8)%N /\
      (trigger_barrier record < 256 ^ N.of_nat 8)%N /\
      (trigger_upper_barrier record < 256 ^ N.of_nat 8)%N /\
      (average_quarterly_turnover record < 256 ^ N.of_nat 8)%N /\
      (trading_scope record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (sicav_counterparty_member record) = 4 /\
      (net_asset_value_indicator record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (reference_trading_venue record) = 1 /\
      (outstanding_capital record < 256 ^ N.of_nat 8)%N /\
      (first_trading_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_system record) = 1 /\
      (number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (number_of_holders record < 256 ^ N.of_nat 4)%N /\
      (outstanding_shares record < 256 ^ N.of_nat 4)%N /\
      (minimum_authorized_shares record < 256 ^ N.of_nat 4)%N /\
      (minimum_capital record < 256 ^ N.of_nat 8)%N /\
      (last_admission_date record < 256 ^ N.of_nat 4)%N /\
      (barrier_return record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (investment_fund_manager record) = 80 /\
      (effective_amount_filters_routed_orders record < 256 ^ N.of_nat 8)%N /\
      (order_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      (investment_fund_class record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (master_fund_name record) = 80 /\
      Datatypes.length (investment_fund_management_company record) = 80 /\
      Datatypes.length (investment_fund_depository record) = 80 /\
      Datatypes.length (investment_fund_category record) = 80 /\
      (investment_fund_minimum_subscription_amount record < 256 ^ N.of_nat 8)%N /\
      (investment_fund_minimum_maintenance_amount record < 256 ^ N.of_nat 8)%N /\
      (investment_fund_cut_off_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (nav_communication_term record) = 1 /\
      (investment_fund_number_of_decimals record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (commodity_derivative_indicator record) = 1 /\
      (double_volume_cap_reached record < 256 ^ N.of_nat 1)%N /\
      (adt record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (base_product record) = 4 /\
      Datatypes.length (sub_product record) = 4 /\
      Datatypes.length (further_sub_product record) = 4 /\
      (adnt record < 256 ^ N.of_nat 8)%N /\
      (price_tick_rule record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 22 /\
      Datatypes.length (underlying_isin record) = 12 /\
      Datatypes.length (underlying_currency record) = 3 /\
      (minimum_display_qty record < 256 ^ N.of_nat 4)%N /\
      (retail_service_flag record < 256 ^ N.of_nat 1)%N /\
      (self_match_prevention record < 256 ^ N.of_nat 1)%N.

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
      encode_bytes 40 (security_name record) ++
      encode_bytes 7 (net_asset_value_identifier record) ++
      encode_bytes 2 (security_sub_type record) ++
      encode_bytes 8 (maturity_month_year record) ++
      encode_bytes 1 (security_status record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 8 (strike_value record) ++
      encode_bytes 1 (exercise_style record) ++
      encode_bytes 1 (put_or_call record) ++
      encode_uint 8 (position_limit record) ++
      encode_uint 8 (nt_position_limit record) ++
      encode_bytes 12 (issuer record) ++
      encode_uint 1 (cp_reg_type record) ++
      encode_uint 8 (barrier record) ++
      encode_uint 4 (last_trading_day record) ++
      encode_uint 1 (automatic_expiration record) ++
      encode_bytes 2 (fee_type record) ++
      encode_uint 8 (barrier_2 record) ++
      encode_uint 8 (trigger_barrier record) ++
      encode_uint 8 (trigger_upper_barrier record) ++
      encode_uint 8 (average_quarterly_turnover record) ++
      encode_uint 1 (trading_scope record) ++
      encode_bytes 4 (sicav_counterparty_member record) ++
      encode_uint 1 (net_asset_value_indicator record) ++
      encode_bytes 1 (reference_trading_venue record) ++
      encode_uint 8 (outstanding_capital record) ++
      encode_uint 4 (first_trading_date record) ++
      encode_bytes 1 (settlement_system record) ++
      encode_uint 1 (number_of_decimals record) ++
      encode_uint 4 (number_of_holders record) ++
      encode_uint 4 (outstanding_shares record) ++
      encode_uint 4 (minimum_authorized_shares record) ++
      encode_uint 8 (minimum_capital record) ++
      encode_uint 4 (last_admission_date record) ++
      encode_uint 8 (barrier_return record) ++
      encode_bytes 80 (investment_fund_manager record) ++
      encode_uint 8 (effective_amount_filters_routed_orders record) ++
      encode_uint 1 (order_number_of_decimals record) ++
      encode_uint 1 (investment_fund_class record) ++
      encode_bytes 80 (master_fund_name record) ++
      encode_bytes 80 (investment_fund_management_company record) ++
      encode_bytes 80 (investment_fund_depository record) ++
      encode_bytes 80 (investment_fund_category record) ++
      encode_uint 8 (investment_fund_minimum_subscription_amount record) ++
      encode_uint 8 (investment_fund_minimum_maintenance_amount record) ++
      encode_uint 8 (investment_fund_cut_off_time record) ++
      encode_bytes 1 (nav_communication_term record) ++
      encode_uint 1 (investment_fund_number_of_decimals record) ++
      encode_bytes 1 (commodity_derivative_indicator record) ++
      encode_uint 1 (double_volume_cap_reached record) ++
      encode_uint 8 (adt record) ++
      encode_bytes 4 (base_product record) ++
      encode_bytes 4 (sub_product record) ++
      encode_bytes 4 (further_sub_product record) ++
      encode_uint 8 (adnt record) ++
      encode_uint 1 (price_tick_rule record) ++
      encode_bytes 22 (underlying_symbol record) ++
      encode_bytes 12 (underlying_isin record) ++
      encode_bytes 3 (underlying_currency record) ++
      encode_uint 4 (minimum_display_qty record) ++
      encode_uint 1 (retail_service_flag record) ++
      encode_uint 1 (self_match_prevention record).

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
                                                                                                              match decode_bytes 40 bytes with
                                                                                                              | None => None
                                                                                                              | Some (security_name_value, bytes) =>
                                                                                                                  match decode_bytes 7 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (net_asset_value_identifier_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (security_sub_type_value, bytes) =>
                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (maturity_month_year_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (security_status_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (strike_price_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (strike_value_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (exercise_style_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (put_or_call_value, bytes) =>
                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (position_limit_value, bytes) =>
                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (nt_position_limit_value, bytes) =>
                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (issuer_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (cp_reg_type_value, bytes) =>
                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (barrier_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (last_trading_day_value, bytes) =>
                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (automatic_expiration_value, bytes) =>
                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (fee_type_value, bytes) =>
                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (barrier_2_value, bytes) =>
                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (trigger_barrier_value, bytes) =>
                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (trigger_upper_barrier_value, bytes) =>
                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (average_quarterly_turnover_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (trading_scope_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (sicav_counterparty_member_value, bytes) =>
                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (net_asset_value_indicator_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (reference_trading_venue_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (outstanding_capital_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (first_trading_date_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (settlement_system_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (number_of_holders_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (outstanding_shares_value, bytes) =>
                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (minimum_authorized_shares_value, bytes) =>
                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (minimum_capital_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (last_admission_date_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (barrier_return_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (investment_fund_manager_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (effective_amount_filters_routed_orders_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (order_number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (investment_fund_class_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (master_fund_name_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (investment_fund_management_company_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (investment_fund_depository_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (investment_fund_category_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (investment_fund_minimum_subscription_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (investment_fund_minimum_maintenance_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (investment_fund_cut_off_time_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (nav_communication_term_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (investment_fund_number_of_decimals_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (commodity_derivative_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (double_volume_cap_reached_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (adt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (base_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (sub_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (further_sub_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (adnt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (price_tick_rule_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (underlying_symbol_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (underlying_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (underlying_currency_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (minimum_display_qty_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (retail_service_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (self_match_prevention_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      Some ({| sequence_number := sequence_number_value; market_id := market_id_value; market_segment_id := market_segment_id_value; security_code := security_code_value; symbol := symbol_value; symbol_isin := symbol_isin_value; fisn := fisn_value; issuer_lei := issuer_lei_value; security_group := security_group_value; cfi_code := cfi_code_value; security_type := security_type_value; maturity_date := maturity_date_value; issue_date := issue_date_value; contract_multiplier := contract_multiplier_value; li_spre := li_spre_value; sst_ipre := sst_ipre_value; li_spost := li_spost_value; sst_ipost := sst_ipost_value; liquid_instrument := liquid_instrument_value; admission_requested_by_issuer := admission_requested_by_issuer_value; min_trade_vol := min_trade_vol_value; round_lot := round_lot_value; currency := currency_value; modality_mask_b_4 := modality_mask_b_4_value; security_description := security_description_value; trading_obligation := trading_obligation_value; security_name := security_name_value; net_asset_value_identifier := net_asset_value_identifier_value; security_sub_type := security_sub_type_value; maturity_month_year := maturity_month_year_value; security_status := security_status_value; strike_price := strike_price_value; strike_value := strike_value_value; exercise_style := exercise_style_value; put_or_call := put_or_call_value; position_limit := position_limit_value; nt_position_limit := nt_position_limit_value; issuer := issuer_value; cp_reg_type := cp_reg_type_value; barrier := barrier_value; last_trading_day := last_trading_day_value; automatic_expiration := automatic_expiration_value; fee_type := fee_type_value; barrier_2 := barrier_2_value; trigger_barrier := trigger_barrier_value; trigger_upper_barrier := trigger_upper_barrier_value; average_quarterly_turnover := average_quarterly_turnover_value; trading_scope := trading_scope_value; sicav_counterparty_member := sicav_counterparty_member_value; net_asset_value_indicator := net_asset_value_indicator_value; reference_trading_venue := reference_trading_venue_value; outstanding_capital := outstanding_capital_value; first_trading_date := first_trading_date_value; settlement_system := settlement_system_value; number_of_decimals := number_of_decimals_value; number_of_holders := number_of_holders_value; outstanding_shares := outstanding_shares_value; minimum_authorized_shares := minimum_authorized_shares_value; minimum_capital := minimum_capital_value; last_admission_date := last_admission_date_value; barrier_return := barrier_return_value; investment_fund_manager := investment_fund_manager_value; effective_amount_filters_routed_orders := effective_amount_filters_routed_orders_value; order_number_of_decimals := order_number_of_decimals_value; investment_fund_class := investment_fund_class_value; master_fund_name := master_fund_name_value; investment_fund_management_company := investment_fund_management_company_value; investment_fund_depository := investment_fund_depository_value; investment_fund_category := investment_fund_category_value; investment_fund_minimum_subscription_amount := investment_fund_minimum_subscription_amount_value; investment_fund_minimum_maintenance_amount := investment_fund_minimum_maintenance_amount_value; investment_fund_cut_off_time := investment_fund_cut_off_time_value; nav_communication_term := nav_communication_term_value; investment_fund_number_of_decimals := investment_fund_number_of_decimals_value; commodity_derivative_indicator := commodity_derivative_indicator_value; double_volume_cap_reached := double_volume_cap_reached_value; adt := adt_value; base_product := base_product_value; sub_product := sub_product_value; further_sub_product := further_sub_product_value; adnt := adnt_value; price_tick_rule := price_tick_rule_value; underlying_symbol := underlying_symbol_value; underlying_isin := underlying_isin_value; underlying_currency := underlying_currency_value; minimum_display_qty := minimum_display_qty_value; retail_service_flag := retail_service_flag_value; self_match_prevention := self_match_prevention_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 976.
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
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_uint by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_uint by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_uint by exact bound_57.
      rewrite decode_encode_uint by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      rewrite decode_encode_uint by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_uint by exact bound_62.
      rewrite decode_encode_uint by exact bound_63.
      rewrite decode_encode_uint by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_uint by exact bound_69.
      rewrite decode_encode_uint by exact bound_70.
      rewrite decode_encode_uint by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_uint by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      rewrite decode_encode_uint by exact bound_75.
      rewrite decode_encode_uint by exact bound_76.
      rewrite decode_encode_bytes by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_uint by exact bound_80.
      rewrite decode_encode_uint by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_bytes by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_uint by exact bound_85.
      rewrite decode_encode_uint by exact bound_86.
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
      reference_price : N;
      static_price : N;
      dynamic_price_oscilation_percentage : N;
      dynamic_range_multiplier : N;
      auction_trigger_price : N;
      auction_end_time : N;
      liquidative_value_date : N;
      bonus_warrants_with_active_bonus : N;
      security_trading_status : N;
      auction_origin : N;
      non_availability_reason : N;
      exemption_situation : list byte;
      block_oscilation_percentage : N;
      high_limit_price : N;
      low_limit_price : N;
      liquidative_value : N;
      static_range_type : list byte;
      order_static_range : N;
      block_static_range : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (static_price record < 256 ^ N.of_nat 8)%N /\
      (dynamic_price_oscilation_percentage record < 256 ^ N.of_nat 8)%N /\
      (dynamic_range_multiplier record < 256 ^ N.of_nat 1)%N /\
      (auction_trigger_price record < 256 ^ N.of_nat 8)%N /\
      (auction_end_time record < 256 ^ N.of_nat 8)%N /\
      (liquidative_value_date record < 256 ^ N.of_nat 4)%N /\
      (bonus_warrants_with_active_bonus record < 256 ^ N.of_nat 1)%N /\
      (security_trading_status record < 256 ^ N.of_nat 1)%N /\
      (auction_origin record < 256 ^ N.of_nat 1)%N /\
      (non_availability_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exemption_situation record) = 1 /\
      (block_oscilation_percentage record < 256 ^ N.of_nat 8)%N /\
      (high_limit_price record < 256 ^ N.of_nat 8)%N /\
      (low_limit_price record < 256 ^ N.of_nat 8)%N /\
      (liquidative_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (static_range_type record) = 1 /\
      (order_static_range record < 256 ^ N.of_nat 8)%N /\
      (block_static_range record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (static_price record) ++
      encode_uint 8 (dynamic_price_oscilation_percentage record) ++
      encode_uint 1 (dynamic_range_multiplier record) ++
      encode_uint 8 (auction_trigger_price record) ++
      encode_uint 8 (auction_end_time record) ++
      encode_uint 4 (liquidative_value_date record) ++
      encode_uint 1 (bonus_warrants_with_active_bonus record) ++
      encode_uint 1 (security_trading_status record) ++
      encode_uint 1 (auction_origin record) ++
      encode_uint 1 (non_availability_reason record) ++
      encode_bytes 1 (exemption_situation record) ++
      encode_uint 8 (block_oscilation_percentage record) ++
      encode_uint 8 (high_limit_price record) ++
      encode_uint 8 (low_limit_price record) ++
      encode_uint 8 (liquidative_value record) ++
      encode_bytes 1 (static_range_type record) ++
      encode_uint 8 (order_static_range record) ++
      encode_uint 8 (block_static_range record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (reference_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (static_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (dynamic_price_oscilation_percentage_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (dynamic_range_multiplier_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (auction_trigger_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (auction_end_time_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (liquidative_value_date_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (bonus_warrants_with_active_bonus_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (security_trading_status_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (auction_origin_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (non_availability_reason_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (exemption_situation_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (block_oscilation_percentage_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (high_limit_price_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (low_limit_price_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (liquidative_value_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (static_range_type_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (order_static_range_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (block_static_range_value, bytes) =>
                                                                                              Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; reference_price := reference_price_value; static_price := static_price_value; dynamic_price_oscilation_percentage := dynamic_price_oscilation_percentage_value; dynamic_range_multiplier := dynamic_range_multiplier_value; auction_trigger_price := auction_trigger_price_value; auction_end_time := auction_end_time_value; liquidative_value_date := liquidative_value_date_value; bonus_warrants_with_active_bonus := bonus_warrants_with_active_bonus_value; security_trading_status := security_trading_status_value; auction_origin := auction_origin_value; non_availability_reason := non_availability_reason_value; exemption_situation := exemption_situation_value; block_oscilation_percentage := block_oscilation_percentage_value; high_limit_price := high_limit_price_value; low_limit_price := low_limit_price_value; liquidative_value := liquidative_value_value; static_range_type := static_range_type_value; order_static_range := order_static_range_value; block_static_range := block_static_range_value |}, bytes)
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 115.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityStatusMessage.

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
      buyer_bolsa_code : list byte;
      settl_date : N;
      transaction_category : list byte;
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
      Datatypes.length (buyer_bolsa_code record) = 1 /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1.

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
      encode_bytes 1 (buyer_bolsa_code record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record).

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
                                                          | Some (buyer_bolsa_code_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (settl_date_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (transaction_category_value, bytes) =>
                                                                      Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; buyer_bolsa_code := buyer_bolsa_code_value; settl_date := settl_date_value; transaction_category := transaction_category_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_15.
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
      buyer_bolsa_code : list byte;
      settl_date : N;
      transaction_category : list byte;
      last_change_flag : N;
      benc_rfpt_flag : list byte;
      trade_price_condition : list byte;
      pre_trade_transparency_waiver : list byte;
      deferral_waiver : list byte;
      publish_date_and_time : N;
      trade_date : N;
      trade_session_date : N;
      volume_float : N;
      sicav_fund_counterparty_side : list byte;
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
      Datatypes.length (buyer_bolsa_code record) = 1 /\
      (settl_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (transaction_category record) = 1 /\
      (last_change_flag record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (benc_rfpt_flag record) = 1 /\
      Datatypes.length (trade_price_condition record) = 1 /\
      Datatypes.length (pre_trade_transparency_waiver record) = 1 /\
      Datatypes.length (deferral_waiver record) = 1 /\
      (publish_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (trade_session_date record < 256 ^ N.of_nat 4)%N /\
      (volume_float record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sicav_fund_counterparty_side record) = 1 /\
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
      encode_bytes 1 (buyer_bolsa_code record) ++
      encode_uint 4 (settl_date record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_uint 1 (last_change_flag record) ++
      encode_bytes 1 (benc_rfpt_flag record) ++
      encode_bytes 1 (trade_price_condition record) ++
      encode_bytes 1 (pre_trade_transparency_waiver record) ++
      encode_bytes 1 (deferral_waiver record) ++
      encode_uint 8 (publish_date_and_time record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 4 (trade_session_date record) ++
      encode_uint 8 (volume_float record) ++
      encode_bytes 1 (sicav_fund_counterparty_side record) ++
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
                                                          | Some (buyer_bolsa_code_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (settl_date_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (transaction_category_value, bytes) =>
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
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (publish_date_and_time_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (trade_date_value, bytes) =>
                                                                                                  match decode_uint 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trade_session_date_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (volume_float_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (sicav_fund_counterparty_side_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (amended_trade_type_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (exec_ref_id_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (amended_trade_date_value, bytes) =>
                                                                                                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; market_segment_id := market_segment_id_value; trading_session_id := trading_session_id_value; trd_match_id := trd_match_id_value; trade_type := trade_type_value; last_px := last_px_value; last_qty := last_qty_value; gross_trade_amt := gross_trade_amt_value; designation := designation_value; market_mechanism := market_mechanism_value; algo_flag := algo_flag_value; buyer_bolsa_code := buyer_bolsa_code_value; settl_date := settl_date_value; transaction_category := transaction_category_value; last_change_flag := last_change_flag_value; benc_rfpt_flag := benc_rfpt_flag_value; trade_price_condition := trade_price_condition_value; pre_trade_transparency_waiver := pre_trade_transparency_waiver_value; deferral_waiver := deferral_waiver_value; publish_date_and_time := publish_date_and_time_value; trade_date := trade_date_value; trade_session_date := trade_session_date_value; volume_float := volume_float_value; sicav_fund_counterparty_side := sicav_fund_counterparty_side_value; amended_trade_type := amended_trade_type_value; exec_ref_id := exec_ref_id_value; amended_trade_date := amended_trade_date_value |}, bytes)
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 98.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 bound_28]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeTradeAmendmentOrCancellationMessage.

  Module TopOfBookRetailMessage.

    (** Specific message for the Retail Service. This message is sent through the UDP channels G/H *)
    Record t := {
      sequence_number : N;
      security_code : N;
      transaction_date_and_time : N;
      bid_orders_1 : N;
      bid_size_1 : N;
      bid_px_1 : N;
      ask_orders_1 : N;
      ask_size_1 : N;
      ask_px_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (security_code record < 256 ^ N.of_nat 4)%N /\
      (transaction_date_and_time record < 256 ^ N.of_nat 8)%N /\
      (bid_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (bid_size_1 record < 256 ^ N.of_nat 4)%N /\
      (bid_px_1 record < 256 ^ N.of_nat 8)%N /\
      (ask_orders_1 record < 256 ^ N.of_nat 2)%N /\
      (ask_size_1 record < 256 ^ N.of_nat 4)%N /\
      (ask_px_1 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (security_code record) ++
      encode_uint 8 (transaction_date_and_time record) ++
      encode_uint 2 (bid_orders_1 record) ++
      encode_uint 4 (bid_size_1 record) ++
      encode_uint 8 (bid_px_1 record) ++
      encode_uint 2 (ask_orders_1 record) ++
      encode_uint 4 (ask_size_1 record) ++
      encode_uint 8 (ask_px_1 record).

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
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_orders_1_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (ask_size_1_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (ask_px_1_value, bytes) =>
                                          Some ({| sequence_number := sequence_number_value; security_code := security_code_value; transaction_date_and_time := transaction_date_and_time_value; bid_orders_1 := bid_orders_1_value; bid_size_1 := bid_size_1_value; bid_px_1 := bid_px_1_value; ask_orders_1 := ask_orders_1_value; ask_size_1 := ask_size_1_value; ask_px_1 := ask_px_1_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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

  End TopOfBookRetailMessage.

End BmeEquitiesRetailV16.
