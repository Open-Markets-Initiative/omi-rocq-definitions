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
      - a Composite rule
      - a run counted by a field
      - the dispatch that chooses a message by its type
  *)

Module SiacCqsSnapshotV21.

  Module LineIntegrityMessage.

    (** Sent to verify continued integrity of multicast transmission *)
    Record t := {
      participant_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          Some ({| participant_id := participant_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End LineIntegrityMessage.

  Module SymbolReferenceDataMessage.

    (** Contains the latest symbol configuration details at the time Snapshot is generated *)
    Record t := {
      participant_id : list byte;
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
      fourth_reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
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
      Datatypes.length (fourth_reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
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
      encode_bytes 1 (fourth_reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
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
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (fourth_reserved_value, bytes) =>
                                                                                  Some ({| participant_id := participant_id_value; security_symbol := security_symbol_value; prior_security_symbol := prior_security_symbol_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; primary_listing_market_previous_closing_price := primary_listing_market_previous_closing_price_value; consolidated_closing_price := consolidated_closing_price_value; round_lot_size := round_lot_size_value; reserved := reserved_value; luld_tier := luld_tier_value; luld_leverage_ratio := luld_leverage_ratio_value; test := test_value; ipo := ipo_value; financial_status_indicator := financial_status_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; halt_reason := halt_reason_value; instrument_type := instrument_type_value; second_reserved := second_reserved_value; third_reserved := third_reserved_value; fourth_reserved := fourth_reserved_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolReferenceDataMessage.

  Module MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage.

    (** Reports the calculated Level 1, Level 2 and Level 3 threshold values for the current trading day necessary to trigger a circuit breaker *)
    Record t := {
      participant_id : list byte;
      mwcb_level_1 : N;
      mwcb_level_2 : N;
      mwcb_level_3 : N;
      reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      (mwcb_level_1 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_2 record < 256 ^ N.of_nat 8)%N /\
      (mwcb_level_3 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      encode_uint 8 (mwcb_level_1 record) ++
      encode_uint 8 (mwcb_level_2 record) ++
      encode_uint 8 (mwcb_level_3 record) ++
      encode_bytes 1 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
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
                          Some ({| participant_id := participant_id_value; mwcb_level_1 := mwcb_level_1_value; mwcb_level_2 := mwcb_level_2_value; mwcb_level_3 := mwcb_level_3_value; reserved := reserved_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketWideCircuitBreakerDeclineLevelStatusSnapshotMessage.

  Module ConsolidatedSnapshotMessage.

    (** SIP generated message reporting latest LULD price bands, auction information, NBBO, and other per-symbol data at the time Snapshot is generated *)
    Record t := {
      participant_id : list byte;
      security_symbol : list byte;
      instrument_type : list byte;
      lower_limit_price_band : N;
      upper_limit_price_band : N;
      auction_collar_reference_price : N;
      auction_collar_upper_threshold_price : N;
      auction_collar_lower_threshold_price : N;
      number_of_extensions : N;
      national_best_bid_participant_id : list byte;
      national_best_bid_quote_condition : list byte;
      national_best_bid_price : N;
      national_best_bid_size : N;
      finra_best_bid_market_maker_id : list byte;
      national_best_offer_participant_id : list byte;
      national_best_offer_quote_condition : list byte;
      national_best_offer_price : N;
      national_best_offer_size : N;
      finra_best_offer_market_maker_id : list byte;
      national_bbo_luld_indicator : list byte;
      primary_listing_market_participant_id : list byte;
      financial_status_indicator : list byte;
      short_sale_restriction_indicator : list byte;
      halt_reason : list byte;
      reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (instrument_type record) = 1 /\
      (lower_limit_price_band record < 256 ^ N.of_nat 8)%N /\
      (upper_limit_price_band record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_reference_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_upper_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (auction_collar_lower_threshold_price record < 256 ^ N.of_nat 8)%N /\
      (number_of_extensions record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (national_best_bid_participant_id record) = 1 /\
      Datatypes.length (national_best_bid_quote_condition record) = 1 /\
      (national_best_bid_price record < 256 ^ N.of_nat 8)%N /\
      (national_best_bid_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (finra_best_bid_market_maker_id record) = 4 /\
      Datatypes.length (national_best_offer_participant_id record) = 1 /\
      Datatypes.length (national_best_offer_quote_condition record) = 1 /\
      (national_best_offer_price record < 256 ^ N.of_nat 8)%N /\
      (national_best_offer_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (finra_best_offer_market_maker_id record) = 4 /\
      Datatypes.length (national_bbo_luld_indicator record) = 1 /\
      Datatypes.length (primary_listing_market_participant_id record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (short_sale_restriction_indicator record) = 1 /\
      Datatypes.length (halt_reason record) = 1 /\
      Datatypes.length (reserved record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (instrument_type record) ++
      encode_uint 8 (lower_limit_price_band record) ++
      encode_uint 8 (upper_limit_price_band record) ++
      encode_uint 8 (auction_collar_reference_price record) ++
      encode_uint 8 (auction_collar_upper_threshold_price record) ++
      encode_uint 8 (auction_collar_lower_threshold_price record) ++
      encode_uint 1 (number_of_extensions record) ++
      encode_bytes 1 (national_best_bid_participant_id record) ++
      encode_bytes 1 (national_best_bid_quote_condition record) ++
      encode_uint 8 (national_best_bid_price record) ++
      encode_uint 4 (national_best_bid_size record) ++
      encode_bytes 4 (finra_best_bid_market_maker_id record) ++
      encode_bytes 1 (national_best_offer_participant_id record) ++
      encode_bytes 1 (national_best_offer_quote_condition record) ++
      encode_uint 8 (national_best_offer_price record) ++
      encode_uint 4 (national_best_offer_size record) ++
      encode_bytes 4 (finra_best_offer_market_maker_id record) ++
      encode_bytes 1 (national_bbo_luld_indicator record) ++
      encode_bytes 1 (primary_listing_market_participant_id record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 1 (short_sale_restriction_indicator record) ++
      encode_bytes 1 (halt_reason record) ++
      encode_bytes 1 (reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (security_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (instrument_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (lower_limit_price_band_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (upper_limit_price_band_value, bytes) =>
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
                                          | Some (national_best_bid_participant_id_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (national_best_bid_quote_condition_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (national_best_bid_price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (national_best_bid_size_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (finra_best_bid_market_maker_id_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (national_best_offer_participant_id_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (national_best_offer_quote_condition_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (national_best_offer_price_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (national_best_offer_size_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (finra_best_offer_market_maker_id_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (national_bbo_luld_indicator_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (primary_listing_market_participant_id_value, bytes) =>
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
                                                                                                      | Some (reserved_value, bytes) =>
                                                                                                          Some ({| participant_id := participant_id_value; security_symbol := security_symbol_value; instrument_type := instrument_type_value; lower_limit_price_band := lower_limit_price_band_value; upper_limit_price_band := upper_limit_price_band_value; auction_collar_reference_price := auction_collar_reference_price_value; auction_collar_upper_threshold_price := auction_collar_upper_threshold_price_value; auction_collar_lower_threshold_price := auction_collar_lower_threshold_price_value; number_of_extensions := number_of_extensions_value; national_best_bid_participant_id := national_best_bid_participant_id_value; national_best_bid_quote_condition := national_best_bid_quote_condition_value; national_best_bid_price := national_best_bid_price_value; national_best_bid_size := national_best_bid_size_value; finra_best_bid_market_maker_id := finra_best_bid_market_maker_id_value; national_best_offer_participant_id := national_best_offer_participant_id_value; national_best_offer_quote_condition := national_best_offer_quote_condition_value; national_best_offer_price := national_best_offer_price_value; national_best_offer_size := national_best_offer_size_value; finra_best_offer_market_maker_id := finra_best_offer_market_maker_id_value; national_bbo_luld_indicator := national_bbo_luld_indicator_value; primary_listing_market_participant_id := primary_listing_market_participant_id_value; financial_status_indicator := financial_status_indicator_value; short_sale_restriction_indicator := short_sale_restriction_indicator_value; halt_reason := halt_reason_value; reserved := reserved_value |}, bytes)
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 96.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConsolidatedSnapshotMessage.

  Module ParticipantSnapshotMessage.

    (** SIP generated message reporting latest participant quote, LULD indicator, price and trading range indications, and halt reason per symbol *)
    Record t := {
      participant_id : list byte;
      security_symbol : list byte;
      quote_condition : list byte;
      bid_price : N;
      bid_size : N;
      offer_price : N;
      offer_size : N;
      retail_interest_indicator : list byte;
      settlement_condition : list byte;
      market_condition : list byte;
      limit_up_limit_down_luld_indicator : list byte;
      high_indication_price : N;
      low_indication_price : N;
      halt_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (quote_condition record) = 1 /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (offer_price record < 256 ^ N.of_nat 8)%N /\
      (offer_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (retail_interest_indicator record) = 1 /\
      Datatypes.length (settlement_condition record) = 1 /\
      Datatypes.length (market_condition record) = 1 /\
      Datatypes.length (limit_up_limit_down_luld_indicator record) = 1 /\
      (high_indication_price record < 256 ^ N.of_nat 8)%N /\
      (low_indication_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (halt_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 8 (bid_price record) ++
      encode_uint 4 (bid_size record) ++
      encode_uint 8 (offer_price record) ++
      encode_uint 4 (offer_size record) ++
      encode_bytes 1 (retail_interest_indicator record) ++
      encode_bytes 1 (settlement_condition record) ++
      encode_bytes 1 (market_condition record) ++
      encode_bytes 1 (limit_up_limit_down_luld_indicator record) ++
      encode_uint 8 (high_indication_price record) ++
      encode_uint 8 (low_indication_price record) ++
      encode_bytes 1 (halt_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (security_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (quote_condition_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_size_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (offer_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (offer_size_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (retail_interest_indicator_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (settlement_condition_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (market_condition_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (limit_up_limit_down_luld_indicator_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (high_indication_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (low_indication_price_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (halt_reason_value, bytes) =>
                                                              Some ({| participant_id := participant_id_value; security_symbol := security_symbol_value; quote_condition := quote_condition_value; bid_price := bid_price_value; bid_size := bid_size_value; offer_price := offer_price_value; offer_size := offer_size_value; retail_interest_indicator := retail_interest_indicator_value; settlement_condition := settlement_condition_value; market_condition := market_condition_value; limit_up_limit_down_luld_indicator := limit_up_limit_down_luld_indicator_value; high_indication_price := high_indication_price_value; low_indication_price := low_indication_price_value; halt_reason := halt_reason_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 58.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParticipantSnapshotMessage.

  Module FinraSnapshotMessage.

    (** SIP generated message reporting FINRA Best Bid and Offer (FBBO) *)
    Record t := {
      participant_id : list byte;
      security_symbol : list byte;
      finra_best_bid_quote_condition : list byte;
      finra_best_bid_price : N;
      finra_best_bid_size : N;
      finra_best_bid_market_maker_id : list byte;
      finra_best_offer_quote_condition : list byte;
      finra_best_offer_price : N;
      finra_best_offer_size : N;
      finra_best_offer_market_maker_id : list byte;
      finra_bbo_luld_indicator : list byte;
      high_indication_price : N;
      low_indication_price : N;
      halt_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (participant_id record) = 1 /\
      Datatypes.length (security_symbol record) = 11 /\
      Datatypes.length (finra_best_bid_quote_condition record) = 1 /\
      (finra_best_bid_price record < 256 ^ N.of_nat 8)%N /\
      (finra_best_bid_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (finra_best_bid_market_maker_id record) = 4 /\
      Datatypes.length (finra_best_offer_quote_condition record) = 1 /\
      (finra_best_offer_price record < 256 ^ N.of_nat 8)%N /\
      (finra_best_offer_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (finra_best_offer_market_maker_id record) = 4 /\
      Datatypes.length (finra_bbo_luld_indicator record) = 1 /\
      (high_indication_price record < 256 ^ N.of_nat 8)%N /\
      (low_indication_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (halt_reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (participant_id record) ++
      encode_bytes 11 (security_symbol record) ++
      encode_bytes 1 (finra_best_bid_quote_condition record) ++
      encode_uint 8 (finra_best_bid_price record) ++
      encode_uint 4 (finra_best_bid_size record) ++
      encode_bytes 4 (finra_best_bid_market_maker_id record) ++
      encode_bytes 1 (finra_best_offer_quote_condition record) ++
      encode_uint 8 (finra_best_offer_price record) ++
      encode_uint 4 (finra_best_offer_size record) ++
      encode_bytes 4 (finra_best_offer_market_maker_id record) ++
      encode_bytes 1 (finra_bbo_luld_indicator record) ++
      encode_uint 8 (high_indication_price record) ++
      encode_uint 8 (low_indication_price record) ++
      encode_bytes 1 (halt_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (participant_id_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (security_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (finra_best_bid_quote_condition_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (finra_best_bid_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (finra_best_bid_size_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (finra_best_bid_market_maker_id_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (finra_best_offer_quote_condition_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (finra_best_offer_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (finra_best_offer_size_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (finra_best_offer_market_maker_id_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (finra_bbo_luld_indicator_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (high_indication_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (low_indication_price_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (halt_reason_value, bytes) =>
                                                              Some ({| participant_id := participant_id_value; security_symbol := security_symbol_value; finra_best_bid_quote_condition := finra_best_bid_quote_condition_value; finra_best_bid_price := finra_best_bid_price_value; finra_best_bid_size := finra_best_bid_size_value; finra_best_bid_market_maker_id := finra_best_bid_market_maker_id_value; finra_best_offer_quote_condition := finra_best_offer_quote_condition_value; finra_best_offer_price := finra_best_offer_price_value; finra_best_offer_size := finra_best_offer_size_value; finra_best_offer_market_maker_id := finra_best_offer_market_maker_id_value; finra_bbo_luld_indicator := finra_bbo_luld_indicator_value; high_indication_price := high_indication_price_value; low_indication_price := low_indication_price_value; halt_reason := halt_reason_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FinraSnapshotMessage.

End SiacCqsSnapshotV21.
