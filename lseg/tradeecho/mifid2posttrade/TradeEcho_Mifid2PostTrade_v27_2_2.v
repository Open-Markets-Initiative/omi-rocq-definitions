From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * London Stock Exchange MiFID II Post Trade

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
      - a field read in bits
  *)

Module TradeEchoMifid2PostTradeV2722.

  Module UnitHeader.

    Record t := {
      length_ : N;
      message_count : N;
      market_data_group : list byte;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_data_group record) = 1 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_bytes 1 (market_data_group record) ++
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; market_data_group := market_data_group_value; sequence_number := sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnitHeader.

  Module MessageHeader.

    (** Gtp Udp Message Header *)
    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  Module SystemEventMessage.

    (** Broadcast at the start and end of day on TRADEcho. Session transition is advertised via one system event message for all instruments allocated to the same multicast channel *)
    Record t := {
      timestamp : N;
      event_code : list byte;
      source_venue : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1 /\
      (source_venue record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 2 (source_venue record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  Some ({| timestamp := timestamp_value; event_code := event_code_value; source_venue := source_venue_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module InstrumentStatusMessage.

    (** Should a specific instrument be subject to individual status change, such as suspension or halt, this will be communicated by the instrument status message *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      trading_status : list byte;
      session_change_reason : N;
      new_end_time : list byte;
      order_book_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (trading_status record) = 1 /\
      (session_change_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (new_end_time record) = 6 /\
      (order_book_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_bytes 1 (trading_status record) ++
      encode_uint 1 (session_change_reason record) ++
      encode_bytes 6 (new_end_time record) ++
      encode_uint 1 (order_book_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (session_change_reason_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (new_end_time_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_book_type_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; trading_status := trading_status_value; session_change_reason := session_change_reason_value; new_end_time := new_end_time_value; order_book_type := order_book_type_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentStatusMessage.

  Module StatisticsMessage.

    (** Contains a set of statistics that are updated frequently, usually as a result of executions *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      volume : N;
      volume_on_book_only : N;
      vwap : N;
      vwap_on_book_only : N;
      number_of_trades : N;
      number_of_trades_on_book_only : N;
      turnover : N;
      turnover_on_book_only : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (volume_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (vwap_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (number_of_trades record < 256 ^ N.of_nat 4)%N /\
      (number_of_trades_on_book_only record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (turnover_on_book_only record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (volume record) ++
      encode_uint 8 (volume_on_book_only record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (vwap_on_book_only record) ++
      encode_uint 4 (number_of_trades record) ++
      encode_uint 4 (number_of_trades_on_book_only record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 8 (turnover_on_book_only record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (volume_on_book_only_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (vwap_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (vwap_on_book_only_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (number_of_trades_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (number_of_trades_on_book_only_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (turnover_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (turnover_on_book_only_value, bytes) =>
                                                  Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; volume := volume_value; volume_on_book_only := volume_on_book_only_value; vwap := vwap_value; vwap_on_book_only := vwap_on_book_only_value; number_of_trades := number_of_trades_value; number_of_trades_on_book_only := number_of_trades_on_book_only_value; turnover := turnover_value; turnover_on_book_only := turnover_on_book_only_value |}, bytes)
                                              end
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

  End StatisticsMessage.

  Module MifidIiTradeReportMessage.

    (** Sent to report the MiFID compliant details of a privately negotiated trade *)
    Record t := {
      timestamp : N;
      instrument : N;
      transaction_identification_code : list byte;
      total_number_of_transactions : N;
      reserved_8 : N;
      source_venue : N;
      price : list byte;
      quantity : list byte;
      trading_date_and_time : list byte;
      instrument_identification_code_type : list byte;
      instrument_identification_code : list byte;
      price_notation : list byte;
      price_major_currency_price_currency : list byte;
      notional_amount : list byte;
      notional_currency : list byte;
      venue_of_execution : list byte;
      publication_date_and_time : list byte;
      benchmark_transaction_flag : list byte;
      agency_cross_trade_flag : list byte;
      non_price_forming_transactions_flag : list byte;
      non_price_contribution_to_discovery : list byte;
      special_dividend_flag : list byte;
      pt_deferral_reason_flag : list byte;
      reference_price_transaction_flag : list byte;
      nt_liquidity_flag : list byte;
      nt_price_conditions_flag : list byte;
      algo_transaction_flag : list byte;
      pt_illiquid_flag : list byte;
      price_improvement_flag : list byte;
      cancellation_flag : list byte;
      amendment_flag : list byte;
      duplicate_flag : list byte;
      exchange_for_physicals_flag : list byte;
      limited_details_flag : list byte;
      ld_full_details_flag : list byte;
      daily_aggregated_transaction_flag : list byte;
      da_full_details_flag : list byte;
      volume_omission_flag : list byte;
      vo_full_details_flag : list byte;
      four_weeks_aggregation_flag : list byte;
      fa_full_details_flag : list byte;
      indefinite_aggregation_flag : list byte;
      volume_omission_for_sovereign_debt_flag : list byte;
      consecutive_aggregation_flag : list byte;
      reserved_1 : N;
      venue_type : N;
      venue_book_definition_id : N;
      notation_of_the_quantity_in_measurement_unit : list byte;
      quantity_in_measurement_unit : list byte;
      transaction_to_be_cleared : list byte;
      emission_allowance_type : list byte;
      venue_of_publication : list byte;
      market_mechanism : list byte;
      trading_mode : list byte;
      transaction_category : list byte;
      negotiation_indicator : list byte;
      agency_cross_indicator : list byte;
      modification_indicator : list byte;
      reference_price_indicator : list byte;
      special_dividend_indicator : list byte;
      off_book_automated_indicator : list byte;
      price_formation_indicator : list byte;
      algorithmic_indicator : list byte;
      post_trade_deferral_reason : list byte;
      deferral_enrichment_type : list byte;
      duplicative_indicator : list byte;
      third_country_trading_venue_of_execution : list byte;
      portfolio_transaction_flag : list byte;
      contingent_transaction_flag : list byte;
      missing_price_price_conditions : list byte;
      market_closing_price_flag : list byte;
      nt_large_in_scale_flag : list byte;
      nt_pre_trade_transparency_flag : list byte;
      effective_date_of_the_contract : list byte;
      maturity_date_of_the_contract : list byte;
      spread : list byte;
      upfront_payment : list byte;
      lei_of_clearing_house : list byte;
      matched_principal_trade_flag : list byte;
      esma_standard_deferral_flags : list byte;
      negotiation_trade_flag : list byte;
      esma_supplementary_deferral_flags : list byte;
      trading_system : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (transaction_identification_code record) = 52 /\
      (total_number_of_transactions record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (price record) = 20 /\
      Datatypes.length (quantity record) = 20 /\
      Datatypes.length (trading_date_and_time record) = 27 /\
      Datatypes.length (instrument_identification_code_type record) = 4 /\
      Datatypes.length (instrument_identification_code record) = 12 /\
      Datatypes.length (price_notation record) = 4 /\
      Datatypes.length (price_major_currency_price_currency record) = 3 /\
      Datatypes.length (notional_amount record) = 20 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (venue_of_execution record) = 4 /\
      Datatypes.length (publication_date_and_time record) = 27 /\
      Datatypes.length (benchmark_transaction_flag record) = 4 /\
      Datatypes.length (agency_cross_trade_flag record) = 4 /\
      Datatypes.length (non_price_forming_transactions_flag record) = 4 /\
      Datatypes.length (non_price_contribution_to_discovery record) = 4 /\
      Datatypes.length (special_dividend_flag record) = 4 /\
      Datatypes.length (pt_deferral_reason_flag record) = 4 /\
      Datatypes.length (reference_price_transaction_flag record) = 4 /\
      Datatypes.length (nt_liquidity_flag record) = 4 /\
      Datatypes.length (nt_price_conditions_flag record) = 4 /\
      Datatypes.length (algo_transaction_flag record) = 4 /\
      Datatypes.length (pt_illiquid_flag record) = 4 /\
      Datatypes.length (price_improvement_flag record) = 4 /\
      Datatypes.length (cancellation_flag record) = 4 /\
      Datatypes.length (amendment_flag record) = 4 /\
      Datatypes.length (duplicate_flag record) = 4 /\
      Datatypes.length (exchange_for_physicals_flag record) = 4 /\
      Datatypes.length (limited_details_flag record) = 4 /\
      Datatypes.length (ld_full_details_flag record) = 4 /\
      Datatypes.length (daily_aggregated_transaction_flag record) = 4 /\
      Datatypes.length (da_full_details_flag record) = 4 /\
      Datatypes.length (volume_omission_flag record) = 4 /\
      Datatypes.length (vo_full_details_flag record) = 4 /\
      Datatypes.length (four_weeks_aggregation_flag record) = 4 /\
      Datatypes.length (fa_full_details_flag record) = 4 /\
      Datatypes.length (indefinite_aggregation_flag record) = 4 /\
      Datatypes.length (volume_omission_for_sovereign_debt_flag record) = 4 /\
      Datatypes.length (consecutive_aggregation_flag record) = 4 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (venue_type record < 256 ^ N.of_nat 1)%N /\
      (venue_book_definition_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (notation_of_the_quantity_in_measurement_unit record) = 25 /\
      Datatypes.length (quantity_in_measurement_unit record) = 20 /\
      Datatypes.length (transaction_to_be_cleared record) = 1 /\
      Datatypes.length (emission_allowance_type record) = 4 /\
      Datatypes.length (venue_of_publication record) = 4 /\
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (transaction_category record) = 1 /\
      Datatypes.length (negotiation_indicator record) = 1 /\
      Datatypes.length (agency_cross_indicator record) = 1 /\
      Datatypes.length (modification_indicator record) = 1 /\
      Datatypes.length (reference_price_indicator record) = 1 /\
      Datatypes.length (special_dividend_indicator record) = 1 /\
      Datatypes.length (off_book_automated_indicator record) = 1 /\
      Datatypes.length (price_formation_indicator record) = 1 /\
      Datatypes.length (algorithmic_indicator record) = 1 /\
      Datatypes.length (post_trade_deferral_reason record) = 1 /\
      Datatypes.length (deferral_enrichment_type record) = 1 /\
      Datatypes.length (duplicative_indicator record) = 1 /\
      Datatypes.length (third_country_trading_venue_of_execution record) = 4 /\
      Datatypes.length (portfolio_transaction_flag record) = 4 /\
      Datatypes.length (contingent_transaction_flag record) = 4 /\
      Datatypes.length (missing_price_price_conditions record) = 4 /\
      Datatypes.length (market_closing_price_flag record) = 4 /\
      Datatypes.length (nt_large_in_scale_flag record) = 4 /\
      Datatypes.length (nt_pre_trade_transparency_flag record) = 4 /\
      Datatypes.length (effective_date_of_the_contract record) = 10 /\
      Datatypes.length (maturity_date_of_the_contract record) = 10 /\
      Datatypes.length (spread record) = 20 /\
      Datatypes.length (upfront_payment record) = 20 /\
      Datatypes.length (lei_of_clearing_house record) = 20 /\
      Datatypes.length (matched_principal_trade_flag record) = 4 /\
      Datatypes.length (esma_standard_deferral_flags record) = 4 /\
      Datatypes.length (negotiation_trade_flag record) = 4 /\
      Datatypes.length (esma_supplementary_deferral_flags record) = 4 /\
      Datatypes.length (trading_system record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_bytes 52 (transaction_identification_code record) ++
      encode_uint 4 (total_number_of_transactions record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_uint 2 (source_venue record) ++
      encode_bytes 20 (price record) ++
      encode_bytes 20 (quantity record) ++
      encode_bytes 27 (trading_date_and_time record) ++
      encode_bytes 4 (instrument_identification_code_type record) ++
      encode_bytes 12 (instrument_identification_code record) ++
      encode_bytes 4 (price_notation record) ++
      encode_bytes 3 (price_major_currency_price_currency record) ++
      encode_bytes 20 (notional_amount record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 4 (venue_of_execution record) ++
      encode_bytes 27 (publication_date_and_time record) ++
      encode_bytes 4 (benchmark_transaction_flag record) ++
      encode_bytes 4 (agency_cross_trade_flag record) ++
      encode_bytes 4 (non_price_forming_transactions_flag record) ++
      encode_bytes 4 (non_price_contribution_to_discovery record) ++
      encode_bytes 4 (special_dividend_flag record) ++
      encode_bytes 4 (pt_deferral_reason_flag record) ++
      encode_bytes 4 (reference_price_transaction_flag record) ++
      encode_bytes 4 (nt_liquidity_flag record) ++
      encode_bytes 4 (nt_price_conditions_flag record) ++
      encode_bytes 4 (algo_transaction_flag record) ++
      encode_bytes 4 (pt_illiquid_flag record) ++
      encode_bytes 4 (price_improvement_flag record) ++
      encode_bytes 4 (cancellation_flag record) ++
      encode_bytes 4 (amendment_flag record) ++
      encode_bytes 4 (duplicate_flag record) ++
      encode_bytes 4 (exchange_for_physicals_flag record) ++
      encode_bytes 4 (limited_details_flag record) ++
      encode_bytes 4 (ld_full_details_flag record) ++
      encode_bytes 4 (daily_aggregated_transaction_flag record) ++
      encode_bytes 4 (da_full_details_flag record) ++
      encode_bytes 4 (volume_omission_flag record) ++
      encode_bytes 4 (vo_full_details_flag record) ++
      encode_bytes 4 (four_weeks_aggregation_flag record) ++
      encode_bytes 4 (fa_full_details_flag record) ++
      encode_bytes 4 (indefinite_aggregation_flag record) ++
      encode_bytes 4 (volume_omission_for_sovereign_debt_flag record) ++
      encode_bytes 4 (consecutive_aggregation_flag record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 1 (venue_type record) ++
      encode_uint 1 (venue_book_definition_id record) ++
      encode_bytes 25 (notation_of_the_quantity_in_measurement_unit record) ++
      encode_bytes 20 (quantity_in_measurement_unit record) ++
      encode_bytes 1 (transaction_to_be_cleared record) ++
      encode_bytes 4 (emission_allowance_type record) ++
      encode_bytes 4 (venue_of_publication record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_bytes 1 (negotiation_indicator record) ++
      encode_bytes 1 (agency_cross_indicator record) ++
      encode_bytes 1 (modification_indicator record) ++
      encode_bytes 1 (reference_price_indicator record) ++
      encode_bytes 1 (special_dividend_indicator record) ++
      encode_bytes 1 (off_book_automated_indicator record) ++
      encode_bytes 1 (price_formation_indicator record) ++
      encode_bytes 1 (algorithmic_indicator record) ++
      encode_bytes 1 (post_trade_deferral_reason record) ++
      encode_bytes 1 (deferral_enrichment_type record) ++
      encode_bytes 1 (duplicative_indicator record) ++
      encode_bytes 4 (third_country_trading_venue_of_execution record) ++
      encode_bytes 4 (portfolio_transaction_flag record) ++
      encode_bytes 4 (contingent_transaction_flag record) ++
      encode_bytes 4 (missing_price_price_conditions record) ++
      encode_bytes 4 (market_closing_price_flag record) ++
      encode_bytes 4 (nt_large_in_scale_flag record) ++
      encode_bytes 4 (nt_pre_trade_transparency_flag record) ++
      encode_bytes 10 (effective_date_of_the_contract record) ++
      encode_bytes 10 (maturity_date_of_the_contract record) ++
      encode_bytes 20 (spread record) ++
      encode_bytes 20 (upfront_payment record) ++
      encode_bytes 20 (lei_of_clearing_house record) ++
      encode_bytes 4 (matched_principal_trade_flag record) ++
      encode_bytes 4 (esma_standard_deferral_flags record) ++
      encode_bytes 4 (negotiation_trade_flag record) ++
      encode_bytes 4 (esma_supplementary_deferral_flags record) ++
      encode_bytes 4 (trading_system record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_bytes 52 bytes with
              | None => None
              | Some (transaction_identification_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (total_number_of_transactions_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (reserved_8_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (source_venue_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (quantity_value, bytes) =>
                                      match decode_bytes 27 bytes with
                                      | None => None
                                      | Some (trading_date_and_time_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (instrument_identification_code_type_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (instrument_identification_code_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (price_notation_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (price_major_currency_price_currency_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (notional_amount_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (notional_currency_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (venue_of_execution_value, bytes) =>
                                                                      match decode_bytes 27 bytes with
                                                                      | None => None
                                                                      | Some (publication_date_and_time_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (benchmark_transaction_flag_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (agency_cross_trade_flag_value, bytes) =>
                                                                                  match decode_bytes 4 bytes with
                                                                                  | None => None
                                                                                  | Some (non_price_forming_transactions_flag_value, bytes) =>
                                                                                      match decode_bytes 4 bytes with
                                                                                      | None => None
                                                                                      | Some (non_price_contribution_to_discovery_value, bytes) =>
                                                                                          match decode_bytes 4 bytes with
                                                                                          | None => None
                                                                                          | Some (special_dividend_flag_value, bytes) =>
                                                                                              match decode_bytes 4 bytes with
                                                                                              | None => None
                                                                                              | Some (pt_deferral_reason_flag_value, bytes) =>
                                                                                                  match decode_bytes 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (reference_price_transaction_flag_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (nt_liquidity_flag_value, bytes) =>
                                                                                                          match decode_bytes 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (nt_price_conditions_flag_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (algo_transaction_flag_value, bytes) =>
                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (pt_illiquid_flag_value, bytes) =>
                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (price_improvement_flag_value, bytes) =>
                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (cancellation_flag_value, bytes) =>
                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (amendment_flag_value, bytes) =>
                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (duplicate_flag_value, bytes) =>
                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (exchange_for_physicals_flag_value, bytes) =>
                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (limited_details_flag_value, bytes) =>
                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ld_full_details_flag_value, bytes) =>
                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (daily_aggregated_transaction_flag_value, bytes) =>
                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (da_full_details_flag_value, bytes) =>
                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (volume_omission_flag_value, bytes) =>
                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (vo_full_details_flag_value, bytes) =>
                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (four_weeks_aggregation_flag_value, bytes) =>
                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (fa_full_details_flag_value, bytes) =>
                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (indefinite_aggregation_flag_value, bytes) =>
                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (volume_omission_for_sovereign_debt_flag_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (consecutive_aggregation_flag_value, bytes) =>
                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (reserved_1_value, bytes) =>
                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (venue_type_value, bytes) =>
                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (venue_book_definition_id_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 25 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (notation_of_the_quantity_in_measurement_unit_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (quantity_in_measurement_unit_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (transaction_to_be_cleared_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (emission_allowance_type_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (venue_of_publication_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (market_mechanism_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (trading_mode_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (transaction_category_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (negotiation_indicator_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (agency_cross_indicator_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (modification_indicator_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (reference_price_indicator_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (special_dividend_indicator_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (off_book_automated_indicator_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (price_formation_indicator_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (algorithmic_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (post_trade_deferral_reason_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (deferral_enrichment_type_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (duplicative_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (third_country_trading_venue_of_execution_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (portfolio_transaction_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (contingent_transaction_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (missing_price_price_conditions_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (market_closing_price_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (nt_large_in_scale_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (nt_pre_trade_transparency_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 10 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (effective_date_of_the_contract_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 10 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (maturity_date_of_the_contract_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (spread_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (upfront_payment_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (lei_of_clearing_house_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (matched_principal_trade_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (esma_standard_deferral_flags_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (negotiation_trade_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (esma_supplementary_deferral_flags_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (trading_system_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  Some ({| timestamp := timestamp_value; instrument := instrument_value; transaction_identification_code := transaction_identification_code_value; total_number_of_transactions := total_number_of_transactions_value; reserved_8 := reserved_8_value; source_venue := source_venue_value; price := price_value; quantity := quantity_value; trading_date_and_time := trading_date_and_time_value; instrument_identification_code_type := instrument_identification_code_type_value; instrument_identification_code := instrument_identification_code_value; price_notation := price_notation_value; price_major_currency_price_currency := price_major_currency_price_currency_value; notional_amount := notional_amount_value; notional_currency := notional_currency_value; venue_of_execution := venue_of_execution_value; publication_date_and_time := publication_date_and_time_value; benchmark_transaction_flag := benchmark_transaction_flag_value; agency_cross_trade_flag := agency_cross_trade_flag_value; non_price_forming_transactions_flag := non_price_forming_transactions_flag_value; non_price_contribution_to_discovery := non_price_contribution_to_discovery_value; special_dividend_flag := special_dividend_flag_value; pt_deferral_reason_flag := pt_deferral_reason_flag_value; reference_price_transaction_flag := reference_price_transaction_flag_value; nt_liquidity_flag := nt_liquidity_flag_value; nt_price_conditions_flag := nt_price_conditions_flag_value; algo_transaction_flag := algo_transaction_flag_value; pt_illiquid_flag := pt_illiquid_flag_value; price_improvement_flag := price_improvement_flag_value; cancellation_flag := cancellation_flag_value; amendment_flag := amendment_flag_value; duplicate_flag := duplicate_flag_value; exchange_for_physicals_flag := exchange_for_physicals_flag_value; limited_details_flag := limited_details_flag_value; ld_full_details_flag := ld_full_details_flag_value; daily_aggregated_transaction_flag := daily_aggregated_transaction_flag_value; da_full_details_flag := da_full_details_flag_value; volume_omission_flag := volume_omission_flag_value; vo_full_details_flag := vo_full_details_flag_value; four_weeks_aggregation_flag := four_weeks_aggregation_flag_value; fa_full_details_flag := fa_full_details_flag_value; indefinite_aggregation_flag := indefinite_aggregation_flag_value; volume_omission_for_sovereign_debt_flag := volume_omission_for_sovereign_debt_flag_value; consecutive_aggregation_flag := consecutive_aggregation_flag_value; reserved_1 := reserved_1_value; venue_type := venue_type_value; venue_book_definition_id := venue_book_definition_id_value; notation_of_the_quantity_in_measurement_unit := notation_of_the_quantity_in_measurement_unit_value; quantity_in_measurement_unit := quantity_in_measurement_unit_value; transaction_to_be_cleared := transaction_to_be_cleared_value; emission_allowance_type := emission_allowance_type_value; venue_of_publication := venue_of_publication_value; market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; transaction_category := transaction_category_value; negotiation_indicator := negotiation_indicator_value; agency_cross_indicator := agency_cross_indicator_value; modification_indicator := modification_indicator_value; reference_price_indicator := reference_price_indicator_value; special_dividend_indicator := special_dividend_indicator_value; off_book_automated_indicator := off_book_automated_indicator_value; price_formation_indicator := price_formation_indicator_value; algorithmic_indicator := algorithmic_indicator_value; post_trade_deferral_reason := post_trade_deferral_reason_value; deferral_enrichment_type := deferral_enrichment_type_value; duplicative_indicator := duplicative_indicator_value; third_country_trading_venue_of_execution := third_country_trading_venue_of_execution_value; portfolio_transaction_flag := portfolio_transaction_flag_value; contingent_transaction_flag := contingent_transaction_flag_value; missing_price_price_conditions := missing_price_price_conditions_value; market_closing_price_flag := market_closing_price_flag_value; nt_large_in_scale_flag := nt_large_in_scale_flag_value; nt_pre_trade_transparency_flag := nt_pre_trade_transparency_flag_value; effective_date_of_the_contract := effective_date_of_the_contract_value; maturity_date_of_the_contract := maturity_date_of_the_contract_value; spread := spread_value; upfront_payment := upfront_payment_value; lei_of_clearing_house := lei_of_clearing_house_value; matched_principal_trade_flag := matched_principal_trade_flag_value; esma_standard_deferral_flags := esma_standard_deferral_flags_value; negotiation_trade_flag := negotiation_trade_flag_value; esma_supplementary_deferral_flags := esma_supplementary_deferral_flags_value; trading_system := trading_system_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 533.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 bound_82]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_bytes by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_bytes by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_bytes by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_bytes by exact bound_54.
      rewrite decode_encode_bytes by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_bytes by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_bytes by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      rewrite decode_encode_bytes by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      rewrite decode_encode_bytes by exact bound_73.
      rewrite decode_encode_bytes by exact bound_74.
      rewrite decode_encode_bytes by exact bound_75.
      rewrite decode_encode_bytes by exact bound_76.
      rewrite decode_encode_bytes by exact bound_77.
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_bytes by exact bound_80.
      rewrite decode_encode_bytes by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MifidIiTradeReportMessage.

End TradeEchoMifid2PostTradeV2722.
