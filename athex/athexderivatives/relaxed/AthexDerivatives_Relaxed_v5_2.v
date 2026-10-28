From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Athens Exchange Group Athens Exchange Derivatives Market Relaxed Channel

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
  *)

Module AthexDerivativesRelaxedV52.

  Module MessageHeader.

    (** Thirty five character header succeeding the Soh character of every message packet *)
    Record t := {
      vendor_identifier : list byte;
      message_category : list byte;
      message_subcategory : list byte;
      venue_i_d : list byte;
      message_sequence_number : list byte;
      publication_timestamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (vendor_identifier record) = 2 /\
      Datatypes.length (message_category record) = 1 /\
      Datatypes.length (message_subcategory record) = 1 /\
      Datatypes.length (venue_i_d record) = 4 /\
      Datatypes.length (message_sequence_number record) = 7 /\
      Datatypes.length (publication_timestamp record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (vendor_identifier record) ++
      encode_bytes 1 (message_category record) ++
      encode_bytes 1 (message_subcategory record) ++
      encode_bytes 4 (venue_i_d record) ++
      encode_bytes 7 (message_sequence_number record) ++
      encode_bytes 20 (publication_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (vendor_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_category_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_subcategory_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (venue_i_d_value, bytes) =>
                      match decode_bytes 7 bytes with
                      | None => None
                      | Some (message_sequence_number_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (publication_timestamp_value, bytes) =>
                              Some ({| vendor_identifier := vendor_identifier_value; message_category := message_category_value; message_subcategory := message_subcategory_value; venue_i_d := venue_i_d_value; message_sequence_number := message_sequence_number_value; publication_timestamp := publication_timestamp_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module ApaPostTradeMessage.

    (** Transmitted whenever a trade is reported to the Ids subsystem, for the Athex Apa post trade transparency service required by Mifid II *)
    Record t := {
      report_status : list byte;
      trading_date_and_time : list byte;
      trade_id_indicator : list byte;
      trade_id : list byte;
      venue : list byte;
      transaction_to_be_cleared : list byte;
      price_notation : list byte;
      price : list byte;
      price_currency : list byte;
      quantity : list byte;
      quantity_currency : list byte;
      notation_of_the_quantity_in_measurement_unit : list byte;
      quantity_in_measurement_unit : list byte;
      notional_amount : list byte;
      notional_currency : list byte;
      instrument_id_type : list byte;
      instrument_id : list byte;
      instrument_full_name : list byte;
      instrument_classification : list byte;
      price_multiplier : list byte;
      underlying_instrument_code : list byte;
      underlying_index_name : list byte;
      term_of_the_underlying_index : list byte;
      option_type : list byte;
      strike_price : list byte;
      strike_price_currency : list byte;
      strike_price_notation : list byte;
      option_exercise_style : list byte;
      maturity_date : list byte;
      expiry_date : list byte;
      delivery_type : list byte;
      type_emission_allowance : list byte;
      otc_post_trade_indicator : list byte;
      deferral_indicator : list byte;
      lmtf : list byte;
      fulf : list byte;
      datf : list byte;
      fula : list byte;
      volo : list byte;
      fulv : list byte;
      fwaf : list byte;
      fulj : list byte;
      idaf : list byte;
      volw : list byte;
      coaf : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (report_status record) = 4 /\
      Datatypes.length (trading_date_and_time record) = 20 /\
      Datatypes.length (trade_id_indicator record) = 1 /\
      Datatypes.length (trade_id record) = 52 /\
      Datatypes.length (venue record) = 4 /\
      Datatypes.length (transaction_to_be_cleared record) = 1 /\
      Datatypes.length (price_notation record) = 4 /\
      Datatypes.length (price record) = 18 /\
      Datatypes.length (price_currency record) = 3 /\
      Datatypes.length (quantity record) = 18 /\
      Datatypes.length (quantity_currency record) = 3 /\
      Datatypes.length (notation_of_the_quantity_in_measurement_unit record) = 25 /\
      Datatypes.length (quantity_in_measurement_unit record) = 18 /\
      Datatypes.length (notional_amount record) = 18 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (instrument_id_type record) = 4 /\
      Datatypes.length (instrument_id record) = 12 /\
      Datatypes.length (instrument_full_name record) = 350 /\
      Datatypes.length (instrument_classification record) = 6 /\
      Datatypes.length (price_multiplier record) = 18 /\
      Datatypes.length (underlying_instrument_code record) = 12 /\
      Datatypes.length (underlying_index_name record) = 25 /\
      Datatypes.length (term_of_the_underlying_index record) = 7 /\
      Datatypes.length (option_type record) = 4 /\
      Datatypes.length (strike_price record) = 18 /\
      Datatypes.length (strike_price_currency record) = 3 /\
      Datatypes.length (strike_price_notation record) = 4 /\
      Datatypes.length (option_exercise_style record) = 4 /\
      Datatypes.length (maturity_date record) = 8 /\
      Datatypes.length (expiry_date record) = 8 /\
      Datatypes.length (delivery_type record) = 4 /\
      Datatypes.length (type_emission_allowance record) = 4 /\
      Datatypes.length (otc_post_trade_indicator record) = 4 /\
      Datatypes.length (deferral_indicator record) = 1 /\
      Datatypes.length (lmtf record) = 1 /\
      Datatypes.length (fulf record) = 1 /\
      Datatypes.length (datf record) = 1 /\
      Datatypes.length (fula record) = 1 /\
      Datatypes.length (volo record) = 1 /\
      Datatypes.length (fulv record) = 1 /\
      Datatypes.length (fwaf record) = 1 /\
      Datatypes.length (fulj record) = 1 /\
      Datatypes.length (idaf record) = 1 /\
      Datatypes.length (volw record) = 1 /\
      Datatypes.length (coaf record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (report_status record) ++
      encode_bytes 20 (trading_date_and_time record) ++
      encode_bytes 1 (trade_id_indicator record) ++
      encode_bytes 52 (trade_id record) ++
      encode_bytes 4 (venue record) ++
      encode_bytes 1 (transaction_to_be_cleared record) ++
      encode_bytes 4 (price_notation record) ++
      encode_bytes 18 (price record) ++
      encode_bytes 3 (price_currency record) ++
      encode_bytes 18 (quantity record) ++
      encode_bytes 3 (quantity_currency record) ++
      encode_bytes 25 (notation_of_the_quantity_in_measurement_unit record) ++
      encode_bytes 18 (quantity_in_measurement_unit record) ++
      encode_bytes 18 (notional_amount record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 4 (instrument_id_type record) ++
      encode_bytes 12 (instrument_id record) ++
      encode_bytes 350 (instrument_full_name record) ++
      encode_bytes 6 (instrument_classification record) ++
      encode_bytes 18 (price_multiplier record) ++
      encode_bytes 12 (underlying_instrument_code record) ++
      encode_bytes 25 (underlying_index_name record) ++
      encode_bytes 7 (term_of_the_underlying_index record) ++
      encode_bytes 4 (option_type record) ++
      encode_bytes 18 (strike_price record) ++
      encode_bytes 3 (strike_price_currency record) ++
      encode_bytes 4 (strike_price_notation record) ++
      encode_bytes 4 (option_exercise_style record) ++
      encode_bytes 8 (maturity_date record) ++
      encode_bytes 8 (expiry_date record) ++
      encode_bytes 4 (delivery_type record) ++
      encode_bytes 4 (type_emission_allowance record) ++
      encode_bytes 4 (otc_post_trade_indicator record) ++
      encode_bytes 1 (deferral_indicator record) ++
      encode_bytes 1 (lmtf record) ++
      encode_bytes 1 (fulf record) ++
      encode_bytes 1 (datf record) ++
      encode_bytes 1 (fula record) ++
      encode_bytes 1 (volo record) ++
      encode_bytes 1 (fulv record) ++
      encode_bytes 1 (fwaf record) ++
      encode_bytes 1 (fulj record) ++
      encode_bytes 1 (idaf record) ++
      encode_bytes 1 (volw record) ++
      encode_bytes 1 (coaf record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (report_status_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (trading_date_and_time_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trade_id_indicator_value, bytes) =>
                  match decode_bytes 52 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (venue_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (transaction_to_be_cleared_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (price_notation_value, bytes) =>
                                  match decode_bytes 18 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (price_currency_value, bytes) =>
                                          match decode_bytes 18 bytes with
                                          | None => None
                                          | Some (quantity_value, bytes) =>
                                              match decode_bytes 3 bytes with
                                              | None => None
                                              | Some (quantity_currency_value, bytes) =>
                                                  match decode_bytes 25 bytes with
                                                  | None => None
                                                  | Some (notation_of_the_quantity_in_measurement_unit_value, bytes) =>
                                                      match decode_bytes 18 bytes with
                                                      | None => None
                                                      | Some (quantity_in_measurement_unit_value, bytes) =>
                                                          match decode_bytes 18 bytes with
                                                          | None => None
                                                          | Some (notional_amount_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (notional_currency_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (instrument_id_type_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (instrument_id_value, bytes) =>
                                                                          match decode_bytes 350 bytes with
                                                                          | None => None
                                                                          | Some (instrument_full_name_value, bytes) =>
                                                                              match decode_bytes 6 bytes with
                                                                              | None => None
                                                                              | Some (instrument_classification_value, bytes) =>
                                                                                  match decode_bytes 18 bytes with
                                                                                  | None => None
                                                                                  | Some (price_multiplier_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (underlying_instrument_code_value, bytes) =>
                                                                                          match decode_bytes 25 bytes with
                                                                                          | None => None
                                                                                          | Some (underlying_index_name_value, bytes) =>
                                                                                              match decode_bytes 7 bytes with
                                                                                              | None => None
                                                                                              | Some (term_of_the_underlying_index_value, bytes) =>
                                                                                                  match decode_bytes 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (option_type_value, bytes) =>
                                                                                                      match decode_bytes 18 bytes with
                                                                                                      | None => None
                                                                                                      | Some (strike_price_value, bytes) =>
                                                                                                          match decode_bytes 3 bytes with
                                                                                                          | None => None
                                                                                                          | Some (strike_price_currency_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (strike_price_notation_value, bytes) =>
                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (option_exercise_style_value, bytes) =>
                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (maturity_date_value, bytes) =>
                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (expiry_date_value, bytes) =>
                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (delivery_type_value, bytes) =>
                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (type_emission_allowance_value, bytes) =>
                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (otc_post_trade_indicator_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (deferral_indicator_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (lmtf_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (fulf_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (datf_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (fula_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (volo_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (fulv_value, bytes) =>
                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (fwaf_value, bytes) =>
                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (fulj_value, bytes) =>
                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (idaf_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (volw_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (coaf_value, bytes) =>
                                                                                                                                                                                          Some ({| report_status := report_status_value; trading_date_and_time := trading_date_and_time_value; trade_id_indicator := trade_id_indicator_value; trade_id := trade_id_value; venue := venue_value; transaction_to_be_cleared := transaction_to_be_cleared_value; price_notation := price_notation_value; price := price_value; price_currency := price_currency_value; quantity := quantity_value; quantity_currency := quantity_currency_value; notation_of_the_quantity_in_measurement_unit := notation_of_the_quantity_in_measurement_unit_value; quantity_in_measurement_unit := quantity_in_measurement_unit_value; notional_amount := notional_amount_value; notional_currency := notional_currency_value; instrument_id_type := instrument_id_type_value; instrument_id := instrument_id_value; instrument_full_name := instrument_full_name_value; instrument_classification := instrument_classification_value; price_multiplier := price_multiplier_value; underlying_instrument_code := underlying_instrument_code_value; underlying_index_name := underlying_index_name_value; term_of_the_underlying_index := term_of_the_underlying_index_value; option_type := option_type_value; strike_price := strike_price_value; strike_price_currency := strike_price_currency_value; strike_price_notation := strike_price_notation_value; option_exercise_style := option_exercise_style_value; maturity_date := maturity_date_value; expiry_date := expiry_date_value; delivery_type := delivery_type_value; type_emission_allowance := type_emission_allowance_value; otc_post_trade_indicator := otc_post_trade_indicator_value; deferral_indicator := deferral_indicator_value; lmtf := lmtf_value; fulf := fulf_value; datf := datf_value; fula := fula_value; volo := volo_value; fulv := fulv_value; fwaf := fwaf_value; fulj := fulj_value; idaf := idaf_value; volw := volw_value; coaf := coaf_value |}, bytes)
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 699.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 bound_44]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
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
      rewrite decode_encode_bytes by exact bound_44.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ApaPostTradeMessage.

  Module ApaPreTradeMessage.

    (** Transmitted whenever a quote is reported to the Ids subsystem by the Athex Apa service, for the Athex Apa pre trade transparency service *)
    Record t := {
      report_status : list byte;
      quote_type : list byte;
      quote_id : list byte;
      event_time : list byte;
      quote_liquidity : list byte;
      venue_mic : list byte;
      submitting_entity_identification_code : list byte;
      price_notation : list byte;
      price : list byte;
      price_currency : list byte;
      quantity : list byte;
      quantity_currency : list byte;
      notation_of_the_quantity_in_measurement_unit : list byte;
      quantity_in_measurement_unit : list byte;
      notional_amount : list byte;
      notional_currency : list byte;
      instrument_id_type : list byte;
      instrument_id : list byte;
      instrument_full_name : list byte;
      instrument_classification : list byte;
      price_multiplier : list byte;
      underlying_instrument_code : list byte;
      underlying_index_name : list byte;
      term_of_the_underlying_index : list byte;
      option_type : list byte;
      strike_price : list byte;
      strike_price_currency : list byte;
      strike_price_notation : list byte;
      option_exercise_style : list byte;
      maturity_date : list byte;
      expiry_date : list byte;
      delivery_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (report_status record) = 4 /\
      Datatypes.length (quote_type record) = 1 /\
      Datatypes.length (quote_id record) = 52 /\
      Datatypes.length (event_time record) = 20 /\
      Datatypes.length (quote_liquidity record) = 1 /\
      Datatypes.length (venue_mic record) = 4 /\
      Datatypes.length (submitting_entity_identification_code record) = 20 /\
      Datatypes.length (price_notation record) = 4 /\
      Datatypes.length (price record) = 18 /\
      Datatypes.length (price_currency record) = 3 /\
      Datatypes.length (quantity record) = 18 /\
      Datatypes.length (quantity_currency record) = 3 /\
      Datatypes.length (notation_of_the_quantity_in_measurement_unit record) = 25 /\
      Datatypes.length (quantity_in_measurement_unit record) = 18 /\
      Datatypes.length (notional_amount record) = 18 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (instrument_id_type record) = 4 /\
      Datatypes.length (instrument_id record) = 12 /\
      Datatypes.length (instrument_full_name record) = 350 /\
      Datatypes.length (instrument_classification record) = 6 /\
      Datatypes.length (price_multiplier record) = 18 /\
      Datatypes.length (underlying_instrument_code record) = 12 /\
      Datatypes.length (underlying_index_name record) = 25 /\
      Datatypes.length (term_of_the_underlying_index record) = 7 /\
      Datatypes.length (option_type record) = 4 /\
      Datatypes.length (strike_price record) = 18 /\
      Datatypes.length (strike_price_currency record) = 3 /\
      Datatypes.length (strike_price_notation record) = 4 /\
      Datatypes.length (option_exercise_style record) = 4 /\
      Datatypes.length (maturity_date record) = 8 /\
      Datatypes.length (expiry_date record) = 8 /\
      Datatypes.length (delivery_type record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (report_status record) ++
      encode_bytes 1 (quote_type record) ++
      encode_bytes 52 (quote_id record) ++
      encode_bytes 20 (event_time record) ++
      encode_bytes 1 (quote_liquidity record) ++
      encode_bytes 4 (venue_mic record) ++
      encode_bytes 20 (submitting_entity_identification_code record) ++
      encode_bytes 4 (price_notation record) ++
      encode_bytes 18 (price record) ++
      encode_bytes 3 (price_currency record) ++
      encode_bytes 18 (quantity record) ++
      encode_bytes 3 (quantity_currency record) ++
      encode_bytes 25 (notation_of_the_quantity_in_measurement_unit record) ++
      encode_bytes 18 (quantity_in_measurement_unit record) ++
      encode_bytes 18 (notional_amount record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 4 (instrument_id_type record) ++
      encode_bytes 12 (instrument_id record) ++
      encode_bytes 350 (instrument_full_name record) ++
      encode_bytes 6 (instrument_classification record) ++
      encode_bytes 18 (price_multiplier record) ++
      encode_bytes 12 (underlying_instrument_code record) ++
      encode_bytes 25 (underlying_index_name record) ++
      encode_bytes 7 (term_of_the_underlying_index record) ++
      encode_bytes 4 (option_type record) ++
      encode_bytes 18 (strike_price record) ++
      encode_bytes 3 (strike_price_currency record) ++
      encode_bytes 4 (strike_price_notation record) ++
      encode_bytes 4 (option_exercise_style record) ++
      encode_bytes 8 (maturity_date record) ++
      encode_bytes 8 (expiry_date record) ++
      encode_bytes 4 (delivery_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (report_status_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (quote_type_value, bytes) =>
              match decode_bytes 52 bytes with
              | None => None
              | Some (quote_id_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (event_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (quote_liquidity_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (venue_mic_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (submitting_entity_identification_code_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (price_notation_value, bytes) =>
                                      match decode_bytes 18 bytes with
                                      | None => None
                                      | Some (price_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (price_currency_value, bytes) =>
                                              match decode_bytes 18 bytes with
                                              | None => None
                                              | Some (quantity_value, bytes) =>
                                                  match decode_bytes 3 bytes with
                                                  | None => None
                                                  | Some (quantity_currency_value, bytes) =>
                                                      match decode_bytes 25 bytes with
                                                      | None => None
                                                      | Some (notation_of_the_quantity_in_measurement_unit_value, bytes) =>
                                                          match decode_bytes 18 bytes with
                                                          | None => None
                                                          | Some (quantity_in_measurement_unit_value, bytes) =>
                                                              match decode_bytes 18 bytes with
                                                              | None => None
                                                              | Some (notional_amount_value, bytes) =>
                                                                  match decode_bytes 3 bytes with
                                                                  | None => None
                                                                  | Some (notional_currency_value, bytes) =>
                                                                      match decode_bytes 4 bytes with
                                                                      | None => None
                                                                      | Some (instrument_id_type_value, bytes) =>
                                                                          match decode_bytes 12 bytes with
                                                                          | None => None
                                                                          | Some (instrument_id_value, bytes) =>
                                                                              match decode_bytes 350 bytes with
                                                                              | None => None
                                                                              | Some (instrument_full_name_value, bytes) =>
                                                                                  match decode_bytes 6 bytes with
                                                                                  | None => None
                                                                                  | Some (instrument_classification_value, bytes) =>
                                                                                      match decode_bytes 18 bytes with
                                                                                      | None => None
                                                                                      | Some (price_multiplier_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (underlying_instrument_code_value, bytes) =>
                                                                                              match decode_bytes 25 bytes with
                                                                                              | None => None
                                                                                              | Some (underlying_index_name_value, bytes) =>
                                                                                                  match decode_bytes 7 bytes with
                                                                                                  | None => None
                                                                                                  | Some (term_of_the_underlying_index_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (option_type_value, bytes) =>
                                                                                                          match decode_bytes 18 bytes with
                                                                                                          | None => None
                                                                                                          | Some (strike_price_value, bytes) =>
                                                                                                              match decode_bytes 3 bytes with
                                                                                                              | None => None
                                                                                                              | Some (strike_price_currency_value, bytes) =>
                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (strike_price_notation_value, bytes) =>
                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (option_exercise_style_value, bytes) =>
                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (maturity_date_value, bytes) =>
                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (expiry_date_value, bytes) =>
                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (delivery_type_value, bytes) =>
                                                                                                                                      Some ({| report_status := report_status_value; quote_type := quote_type_value; quote_id := quote_id_value; event_time := event_time_value; quote_liquidity := quote_liquidity_value; venue_mic := venue_mic_value; submitting_entity_identification_code := submitting_entity_identification_code_value; price_notation := price_notation_value; price := price_value; price_currency := price_currency_value; quantity := quantity_value; quantity_currency := quantity_currency_value; notation_of_the_quantity_in_measurement_unit := notation_of_the_quantity_in_measurement_unit_value; quantity_in_measurement_unit := quantity_in_measurement_unit_value; notional_amount := notional_amount_value; notional_currency := notional_currency_value; instrument_id_type := instrument_id_type_value; instrument_id := instrument_id_value; instrument_full_name := instrument_full_name_value; instrument_classification := instrument_classification_value; price_multiplier := price_multiplier_value; underlying_instrument_code := underlying_instrument_code_value; underlying_index_name := underlying_index_name_value; term_of_the_underlying_index := term_of_the_underlying_index_value; option_type := option_type_value; strike_price := strike_price_value; strike_price_currency := strike_price_currency_value; strike_price_notation := strike_price_notation_value; option_exercise_style := option_exercise_style_value; maturity_date := maturity_date_value; expiry_date := expiry_date_value; delivery_type := delivery_type_value |}, bytes)
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 699.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 bound_31]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ApaPreTradeMessage.

End AthexDerivativesRelaxedV52.
