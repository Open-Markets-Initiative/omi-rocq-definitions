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

Module OnyxFuturesTopOfMarketV10B.

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

    (** used to disseminate all Simple Instruments traded on MIAX FuturesOnyx for the current trading session *)
    Record t := {
      timestamp : N;
      instrument_id : N;
      underlying_asset_type : list byte;
      underlying_asset : list byte;
      product_group_code : list byte;
      exchange : list byte;
      instrument_id_source : list byte;
      instrument_type : list byte;
      maturity_month_year : N;
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
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_asset_type record) = 1 /\
      Datatypes.length (underlying_asset record) = 4 /\
      Datatypes.length (product_group_code record) = 6 /\
      Datatypes.length (exchange record) = 4 /\
      Datatypes.length (instrument_id_source record) = 1 /\
      Datatypes.length (instrument_type record) = 1 /\
      (maturity_month_year record < 256 ^ N.of_nat 4)%N /\
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
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (underlying_asset_type record) ++
      encode_bytes 4 (underlying_asset record) ++
      encode_bytes 6 (product_group_code record) ++
      encode_bytes 4 (exchange record) ++
      encode_bytes 1 (instrument_id_source record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_uint 4 (maturity_month_year record) ++
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
      encode_bytes 16 (reserved_16 record).

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
                  | Some (underlying_asset_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (product_group_code_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (exchange_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (instrument_id_source_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (instrument_type_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (maturity_month_year_value, bytes) =>
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
                                                                                                          match decode_bytes 16 bytes with
                                                                                                          | None => None
                                                                                                          | Some (reserved_16_value, bytes) =>
                                                                                                              Some ({| timestamp := timestamp_value; instrument_id := instrument_id_value; underlying_asset_type := underlying_asset_type_value; underlying_asset := underlying_asset_value; product_group_code := product_group_code_value; exchange := exchange_value; instrument_id_source := instrument_id_source_value; instrument_type := instrument_type_value; maturity_month_year := maturity_month_year_value; currency := currency_value; settlement_currency := settlement_currency_value; match_algorithm := match_algorithm_value; minimum_size := minimum_size_value; maximum_size := maximum_size_value; tick := tick_value; unit_of_measure := unit_of_measure_value; unit_of_measure_quantity := unit_of_measure_quantity_value; settlement_price := settlement_price_value; settlement_price_type_calc_method := settlement_price_type_calc_method_value; total_volume := total_volume_value; open_interest_quantity := open_interest_quantity_value; high_limit_price := high_limit_price_value; low_limit_price := low_limit_price_value; trading_collar_variation_type := trading_collar_variation_type_value; trading_collar_variation := trading_collar_variation_value; reserved_16 := reserved_16_value |}, bytes)
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 119.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleInstrumentDefinitionMessage.

  Module SystemStateMessage.

    Record t := {
      timestamp : N;
      tom_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (tom_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (tom_version record) ++
      encode_uint 1 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (tom_version_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| timestamp := timestamp_value; tom_version := tom_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
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

    (** Used to notify firms of changes to the trading status of a particular Simple or Complex instrument *)
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

    (** used to publish MIAX Futures Onyx Best Bid and Offer (MBBO) of a Simple Instrument or Complex Instrument *)
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

    (** used to disseminate trades that are resulting from executions on MIAX Futures Onyx during the current trading session *)
    Record t := {
      timestamp : N;
      instrument_id : N;
      trade_id : N;
      price : N;
      size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (size_value, bytes) =>
                          Some ({| timestamp := timestamp_value; instrument_id := instrument_id_value; trade_id := trade_id_value; price := price_value; size := size_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End LastSaleMessage.

  Module TradeCancelMessage.

    (** used to publish cancellation of a Simple Instrument trade which was previously published via an Order Execution Message *)
    Record t := {
      timestamp : N;
      trade_date : N;
      instrument_id : N;
      trade_id : N;
      correction_number : N;
      price : N;
      size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (correction_number record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 1 (correction_number record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (size record).

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
                                  Some ({| timestamp := timestamp_value; trade_date := trade_date_value; instrument_id := instrument_id_value; trade_id := trade_id_value; correction_number := correction_number_value; price := price_value; size := size_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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

  End TradeCancelMessage.

End OnyxFuturesTopOfMarketV10B.
