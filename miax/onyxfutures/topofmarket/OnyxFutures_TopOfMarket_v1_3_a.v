From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Top Of Market

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
      - a length prefix framing what follows
      - a run counted by a field
  *)

Module OnyxFuturesTopOfMarketV13A.

  Module MachPacketHeader.

    (** Mach packet header (12 bytes) *)
    Record t := {
      sequence_number : N;
      packet_length : N;
      packet_type : N;
      session_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_type record < 256 ^ N.of_nat 1)%N /\
      (session_number record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (packet_length record) ++
      encode_uint 1 (packet_type record) ++
      encode_uint 1 (session_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (packet_length_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (packet_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_number_value, bytes) =>
                      Some ({| sequence_number := sequence_number_value; packet_length := packet_length_value; packet_type := packet_type_value; session_number := session_number_value |}, bytes)
                  end
              end
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

  End MachPacketHeader.

  Module SimpleInstrumentDefinitionMessage.

    (** Simple Instrument Definition *)
    Record t := {
      timestamp : N;
      instrument_id : N;
      underlying_asset_type : list byte;
      underlying_asset_alphanumeric_4 : list byte;
      product_group_code_alphanumeric_6 : list byte;
      exchange : list byte;
      instrument_id_source : list byte;
      instrument_type : list byte;
      instrument_listing_status : list byte;
      reserved_3 : N;
      currency : list byte;
      settlement_currency : list byte;
      match_algorithm : list byte;
      minimum_size : N;
      maximum_size : N;
      tick : N;
      unit_of_measure : list byte;
      unit_of_measure_quantity : N;
      settlement_price : N;
      settlement_price_type_calc_method : list byte;
      total_volume : N;
      open_interest_quantity : N;
      high_limit_price : N;
      low_limit_price : N;
      trading_collar_variation_type : list byte;
      trading_collar_variation : N;
      contract_date : N;
      maturity_date : N;
      valuation_date : N;
      first_trade_date : N;
      last_trade_date : N;
      first_notice_date : N;
      last_notice_date : N;
      first_delivery_date : N;
      last_delivery_date : N;
      option_strike_price : N;
      option_strike_currency : list byte;
      option_type : list byte;
      option_expiration_type : list byte;
      underlying_future_instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_asset_type record) = 1 /\
      Datatypes.length (underlying_asset_alphanumeric_4 record) = 4 /\
      Datatypes.length (product_group_code_alphanumeric_6 record) = 6 /\
      Datatypes.length (exchange record) = 4 /\
      Datatypes.length (instrument_id_source record) = 1 /\
      Datatypes.length (instrument_type record) = 1 /\
      Datatypes.length (instrument_listing_status record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N /\
      Datatypes.length (currency record) = 1 /\
      Datatypes.length (settlement_currency record) = 1 /\
      Datatypes.length (match_algorithm record) = 1 /\
      (minimum_size record < 256 ^ N.of_nat 4)%N /\
      (maximum_size record < 256 ^ N.of_nat 4)%N /\
      (tick record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (unit_of_measure record) = 5 /\
      (unit_of_measure_quantity record < 256 ^ N.of_nat 4)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (settlement_price_type_calc_method record) = 1 /\
      (total_volume record < 256 ^ N.of_nat 4)%N /\
      (open_interest_quantity record < 256 ^ N.of_nat 4)%N /\
      (high_limit_price record < 256 ^ N.of_nat 8)%N /\
      (low_limit_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trading_collar_variation_type record) = 1 /\
      (trading_collar_variation record < 256 ^ N.of_nat 8)%N /\
      (contract_date record < 256 ^ N.of_nat 4)%N /\
      (maturity_date record < 256 ^ N.of_nat 2)%N /\
      (valuation_date record < 256 ^ N.of_nat 2)%N /\
      (first_trade_date record < 256 ^ N.of_nat 2)%N /\
      (last_trade_date record < 256 ^ N.of_nat 2)%N /\
      (first_notice_date record < 256 ^ N.of_nat 2)%N /\
      (last_notice_date record < 256 ^ N.of_nat 2)%N /\
      (first_delivery_date record < 256 ^ N.of_nat 2)%N /\
      (last_delivery_date record < 256 ^ N.of_nat 2)%N /\
      (option_strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (option_strike_currency record) = 1 /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (option_expiration_type record) = 1 /\
      (underlying_future_instrument_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (underlying_asset_type record) ++
      encode_bytes 4 (underlying_asset_alphanumeric_4 record) ++
      encode_bytes 6 (product_group_code_alphanumeric_6 record) ++
      encode_bytes 4 (exchange record) ++
      encode_bytes 1 (instrument_id_source record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_bytes 1 (instrument_listing_status record) ++
      encode_uint 3 (reserved_3 record) ++
      encode_bytes 1 (currency record) ++
      encode_bytes 1 (settlement_currency record) ++
      encode_bytes 1 (match_algorithm record) ++
      encode_uint 4 (minimum_size record) ++
      encode_uint 4 (maximum_size record) ++
      encode_uint 8 (tick record) ++
      encode_bytes 5 (unit_of_measure record) ++
      encode_uint 4 (unit_of_measure_quantity record) ++
      encode_uint 8 (settlement_price record) ++
      encode_bytes 1 (settlement_price_type_calc_method record) ++
      encode_uint 4 (total_volume record) ++
      encode_uint 4 (open_interest_quantity record) ++
      encode_uint 8 (high_limit_price record) ++
      encode_uint 8 (low_limit_price record) ++
      encode_bytes 1 (trading_collar_variation_type record) ++
      encode_uint 8 (trading_collar_variation record) ++
      encode_uint 4 (contract_date record) ++
      encode_uint 2 (maturity_date record) ++
      encode_uint 2 (valuation_date record) ++
      encode_uint 2 (first_trade_date record) ++
      encode_uint 2 (last_trade_date record) ++
      encode_uint 2 (first_notice_date record) ++
      encode_uint 2 (last_notice_date record) ++
      encode_uint 2 (first_delivery_date record) ++
      encode_uint 2 (last_delivery_date record) ++
      encode_uint 8 (option_strike_price record) ++
      encode_bytes 1 (option_strike_currency record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 1 (option_expiration_type record) ++
      encode_uint 4 (underlying_future_instrument_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (underlying_asset_type_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (underlying_asset_alphanumeric_4_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (product_group_code_alphanumeric_6_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (exchange_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_id_source_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (instrument_type_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (instrument_listing_status_value, bytes) =>
                                          match decode_uint 3 bytes with
                                          | None => None
                                          | Some (reserved_3_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (currency_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (settlement_currency_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (match_algorithm_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (minimum_size_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (maximum_size_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (tick_value, bytes) =>
                                                                      match decode_bytes 5 bytes with
                                                                      | None => None
                                                                      | Some (unit_of_measure_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (unit_of_measure_quantity_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (settlement_price_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (settlement_price_type_calc_method_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (total_volume_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (open_interest_quantity_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (high_limit_price_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (low_limit_price_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (trading_collar_variation_type_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (trading_collar_variation_value, bytes) =>
                                                                                                              match decode_uint 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (contract_date_value, bytes) =>
                                                                                                                  match decode_uint 2 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (maturity_date_value, bytes) =>
                                                                                                                      match decode_uint 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (valuation_date_value, bytes) =>
                                                                                                                          match decode_uint 2 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (first_trade_date_value, bytes) =>
                                                                                                                              match decode_uint 2 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (last_trade_date_value, bytes) =>
                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (first_notice_date_value, bytes) =>
                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (last_notice_date_value, bytes) =>
                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (first_delivery_date_value, bytes) =>
                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (last_delivery_date_value, bytes) =>
                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (option_strike_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (option_strike_currency_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (option_type_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (option_expiration_type_value, bytes) =>
                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (underlying_future_instrument_id_value, bytes) =>
                                                                                                                                                                      Some ({| timestamp := timestamp_value; instrument_id := instrument_id_value; underlying_asset_type := underlying_asset_type_value; underlying_asset_alphanumeric_4 := underlying_asset_alphanumeric_4_value; product_group_code_alphanumeric_6 := product_group_code_alphanumeric_6_value; exchange := exchange_value; instrument_id_source := instrument_id_source_value; instrument_type := instrument_type_value; instrument_listing_status := instrument_listing_status_value; reserved_3 := reserved_3_value; currency := currency_value; settlement_currency := settlement_currency_value; match_algorithm := match_algorithm_value; minimum_size := minimum_size_value; maximum_size := maximum_size_value; tick := tick_value; unit_of_measure := unit_of_measure_value; unit_of_measure_quantity := unit_of_measure_quantity_value; settlement_price := settlement_price_value; settlement_price_type_calc_method := settlement_price_type_calc_method_value; total_volume := total_volume_value; open_interest_quantity := open_interest_quantity_value; high_limit_price := high_limit_price_value; low_limit_price := low_limit_price_value; trading_collar_variation_type := trading_collar_variation_type_value; trading_collar_variation := trading_collar_variation_value; contract_date := contract_date_value; maturity_date := maturity_date_value; valuation_date := valuation_date_value; first_trade_date := first_trade_date_value; last_trade_date := last_trade_date_value; first_notice_date := first_notice_date_value; last_notice_date := last_notice_date_value; first_delivery_date := first_delivery_date_value; last_delivery_date := last_delivery_date_value; option_strike_price := option_strike_price_value; option_strike_currency := option_strike_currency_value; option_type := option_type_value; option_expiration_type := option_expiration_type_value; underlying_future_instrument_id := underlying_future_instrument_id_value |}, bytes)
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 138.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 bound_39]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
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
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleInstrumentDefinitionMessage.

  Module SystemStateMessage.

    (** System State *)
    Record t := {
      timestamp : N;
      to_m_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (to_m_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (to_m_version record) ++
      encode_uint 1 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (to_m_version_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| timestamp := timestamp_value; to_m_version := to_m_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemStateMessage.

  Module InstrumentTradingStatusNotificationMessage.

    (** Instrument Trading Status Notification *)
    Record t := {
      timestamp : N;
      instrument_id : N;
      trading_status : N;
      market_state : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trading_status record < 256 ^ N.of_nat 1)%N /\
      (market_state record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (trading_status record) ++
      encode_uint 1 (market_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_state_value, bytes) =>
                      Some ({| timestamp := timestamp_value; instrument_id := instrument_id_value; trading_status := trading_status_value; market_state := market_state_value |}, bytes)
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

  End InstrumentTradingStatusNotificationMessage.

  Module BestBidAndOfferMessage.

    (** Top of Market (Best Bid and Offer) Message *)
    Record t := {
      timestamp : N;
      instrument_id : N;
      mbb_price : N;
      mbb_size : N;
      mbo_price : N;
      mbo_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (mbb_price record < 256 ^ N.of_nat 8)%N /\
      (mbb_size record < 256 ^ N.of_nat 4)%N /\
      (mbo_price record < 256 ^ N.of_nat 8)%N /\
      (mbo_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (mbb_price record) ++
      encode_uint 4 (mbb_size record) ++
      encode_uint 8 (mbo_price record) ++
      encode_uint 4 (mbo_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (mbb_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (mbb_size_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (mbo_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (mbo_size_value, bytes) =>
                              Some ({| timestamp := timestamp_value; instrument_id := instrument_id_value; mbb_price := mbb_price_value; mbb_size := mbb_size_value; mbo_price := mbo_price_value; mbo_size := mbo_size_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BestBidAndOfferMessage.

  Module LastSaleMessage.

    (** Last Sale (Trade) Message *)
    Record t := {
      timestamp : N;
      trade_date : N;
      instrument_id : N;
      trade_id : N;
      correction_number : N;
      price : N;
      size : N;
      trade_type : list byte;
      complex_trade_id : N;
      instrument_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (correction_number record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (complex_trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (instrument_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 1 (correction_number record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (size record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (complex_trade_id record) ++
      encode_bytes 1 (instrument_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (correction_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (size_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_type_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (complex_trade_id_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (instrument_type_value, bytes) =>
                                              Some ({| timestamp := timestamp_value; trade_date := trade_date_value; instrument_id := instrument_id_value; trade_id := trade_id_value; correction_number := correction_number_value; price := price_value; size := size_value; trade_type := trade_type_value; complex_trade_id := complex_trade_id_value; instrument_type := instrument_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastSaleMessage.

  Module TradeCancelMessage.

    (** Trade Cancel Message *)
    Record t := {
      timestamp : N;
      trade_date : N;
      instrument_id : N;
      trade_id : N;
      correction_number : N;
      price : N;
      size : N;
      instrument_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (correction_number record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (instrument_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 1 (correction_number record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (size record) ++
      encode_bytes 1 (instrument_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (correction_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (size_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (instrument_type_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; trade_date := trade_date_value; instrument_id := instrument_id_value; trade_id := trade_id_value; correction_number := correction_number_value; price := price_value; size := size_value; instrument_type := instrument_type_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCancelMessage.

End OnyxFuturesTopOfMarketV13A.
