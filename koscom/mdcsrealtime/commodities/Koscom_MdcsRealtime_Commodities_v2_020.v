From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Koscom Co., Ltd. MDCS Realtime Commodities

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
  *)

Module KoscomMdcsRealtimeCommoditiesV2020.

  Module PollingDataMessage.

    (** Polling data transmitted at one-minute intervals on every market data feed. Carries Current Time as a heartbeat. *)
    Record t := {
      current_time : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (current_time record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (current_time record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (current_time_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (end_keyword_value, bytes) =>
              Some ({| current_time := current_time_value; end_keyword := end_keyword_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End PollingDataMessage.

  Module KrxIndexMessage.

    (** Krx Index real-time message. Reports current index value, change against previous day, accumulated trading volume, and accumulated trading value for one index. The Index ID field identifies which index group (KRX Index Group 1/2/3, Sector A/B, Gold Spot, or Equity Derivatives) this record belongs to. *)
    Record t := {
      index_id : list byte;
      isin_code : list byte;
      calculation_time : list byte;
      index : list byte;
      index_change_sign_against_the_previous_day : list byte;
      index_change_against_the_previous_day : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (calculation_time record) = 6 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (index_change_sign_against_the_previous_day record) = 1 /\
      Datatypes.length (index_change_against_the_previous_day record) = 9 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (calculation_time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (index_change_sign_against_the_previous_day record) ++
      encode_bytes 9 (index_change_against_the_previous_day record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (index_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (calculation_time_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (index_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (index_change_sign_against_the_previous_day_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (index_change_against_the_previous_day_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (accumulated_trading_volume_value, bytes) =>
                                  match decode_bytes 22 bytes with
                                  | None => None
                                  | Some (accumulated_trading_value_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (filler_4_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| index_id := index_id_value; isin_code := isin_code_value; calculation_time := calculation_time_value; index := index_value; index_change_sign_against_the_previous_day := index_change_sign_against_the_previous_day_value; index_change_against_the_previous_day := index_change_against_the_previous_day_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 82.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End KrxIndexMessage.

  Module KrxEstimatedIndexMessage.

    (** Krx Estimated Index real-time message. Reports the estimated index value during the pre-opening simultaneous-trading window or during regular session estimation. Identical field layout to the Krx Index Message. *)
    Record t := {
      index_id : list byte;
      isin_code : list byte;
      calculation_time : list byte;
      index : list byte;
      index_change_sign_against_the_previous_day : list byte;
      index_change_against_the_previous_day : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (calculation_time record) = 6 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (index_change_sign_against_the_previous_day record) = 1 /\
      Datatypes.length (index_change_against_the_previous_day record) = 9 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (calculation_time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (index_change_sign_against_the_previous_day record) ++
      encode_bytes 9 (index_change_against_the_previous_day record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (index_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (calculation_time_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (index_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (index_change_sign_against_the_previous_day_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (index_change_against_the_previous_day_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (accumulated_trading_volume_value, bytes) =>
                                  match decode_bytes 22 bytes with
                                  | None => None
                                  | Some (accumulated_trading_value_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (filler_4_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| index_id := index_id_value; isin_code := isin_code_value; calculation_time := calculation_time_value; index := index_value; index_change_sign_against_the_previous_day := index_change_sign_against_the_previous_day_value; index_change_against_the_previous_day := index_change_against_the_previous_day_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 82.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End KrxEstimatedIndexMessage.

  Module GlobalIndexMessage.

    (** Global Index real-time message. Reports the current value of a foreign index referenced by KRX (e.g. Korea-Taiwan IT Premier, Korea-China Index) in the index's native currency. *)
    Record t := {
      index_id : list byte;
      isin_code : list byte;
      business_date : list byte;
      calculation_time : list byte;
      index : list byte;
      index_change_sign_against_the_previous_day : list byte;
      index_change_against_the_previous_day : list byte;
      currency_code : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (calculation_time record) = 6 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (index_change_sign_against_the_previous_day record) = 1 /\
      Datatypes.length (index_change_against_the_previous_day record) = 9 /\
      Datatypes.length (currency_code record) = 6 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 6 (calculation_time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (index_change_sign_against_the_previous_day record) ++
      encode_bytes 9 (index_change_against_the_previous_day record) ++
      encode_bytes 6 (currency_code record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (index_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (business_date_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (calculation_time_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (index_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (index_change_sign_against_the_previous_day_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (index_change_against_the_previous_day_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (currency_code_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (filler_4_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| index_id := index_id_value; isin_code := isin_code_value; business_date := business_date_value; calculation_time := calculation_time_value; index := index_value; index_change_sign_against_the_previous_day := index_change_sign_against_the_previous_day_value; index_change_against_the_previous_day := index_change_against_the_previous_day_value; currency_code := currency_code_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GlobalIndexMessage.

  Module BondPrimeIndexMessage.

    (** Bond Prime Index intraday calculation. Reports clean and total-earnings index values plus their weighted variants and average duration / convexity / yield for one Group Code and Maturity Code pair. *)
    Record t := {
      calculating_date : list byte;
      calculating_time : list byte;
      group_code : list byte;
      maturity_code : list byte;
      clean_price_index_krx : list byte;
      total_earnings_index : list byte;
      clean_price_index_weight : list byte;
      total_earnings_index_weight : list byte;
      weight_of_clean_index_value_for_integrity_index_weight : list byte;
      weight_of_sum_index_value_for_integrity_index_weight : list byte;
      average_duration : list byte;
      average_convexity : list byte;
      average_yld : list byte;
      transmission_time : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (calculating_date record) = 8 /\
      Datatypes.length (calculating_time record) = 8 /\
      Datatypes.length (group_code record) = 5 /\
      Datatypes.length (maturity_code record) = 3 /\
      Datatypes.length (clean_price_index_krx record) = 16 /\
      Datatypes.length (total_earnings_index record) = 16 /\
      Datatypes.length (clean_price_index_weight record) = 16 /\
      Datatypes.length (total_earnings_index_weight record) = 16 /\
      Datatypes.length (weight_of_clean_index_value_for_integrity_index_weight record) = 16 /\
      Datatypes.length (weight_of_sum_index_value_for_integrity_index_weight record) = 16 /\
      Datatypes.length (average_duration record) = 16 /\
      Datatypes.length (average_convexity record) = 16 /\
      Datatypes.length (average_yld record) = 16 /\
      Datatypes.length (transmission_time record) = 8 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (calculating_date record) ++
      encode_bytes 8 (calculating_time record) ++
      encode_bytes 5 (group_code record) ++
      encode_bytes 3 (maturity_code record) ++
      encode_bytes 16 (clean_price_index_krx record) ++
      encode_bytes 16 (total_earnings_index record) ++
      encode_bytes 16 (clean_price_index_weight record) ++
      encode_bytes 16 (total_earnings_index_weight record) ++
      encode_bytes 16 (weight_of_clean_index_value_for_integrity_index_weight record) ++
      encode_bytes 16 (weight_of_sum_index_value_for_integrity_index_weight record) ++
      encode_bytes 16 (average_duration record) ++
      encode_bytes 16 (average_convexity record) ++
      encode_bytes 16 (average_yld record) ++
      encode_bytes 8 (transmission_time record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (calculating_date_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (calculating_time_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (group_code_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (maturity_code_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (clean_price_index_krx_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (total_earnings_index_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (clean_price_index_weight_value, bytes) =>
                                  match decode_bytes 16 bytes with
                                  | None => None
                                  | Some (total_earnings_index_weight_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (weight_of_clean_index_value_for_integrity_index_weight_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (weight_of_sum_index_value_for_integrity_index_weight_value, bytes) =>
                                              match decode_bytes 16 bytes with
                                              | None => None
                                              | Some (average_duration_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (average_convexity_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (average_yld_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (transmission_time_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (end_keyword_value, bytes) =>
                                                                  Some ({| calculating_date := calculating_date_value; calculating_time := calculating_time_value; group_code := group_code_value; maturity_code := maturity_code_value; clean_price_index_krx := clean_price_index_krx_value; total_earnings_index := total_earnings_index_value; clean_price_index_weight := clean_price_index_weight_value; total_earnings_index_weight := total_earnings_index_weight_value; weight_of_clean_index_value_for_integrity_index_weight := weight_of_clean_index_value_for_integrity_index_weight_value; weight_of_sum_index_value_for_integrity_index_weight := weight_of_sum_index_value_for_integrity_index_weight_value; average_duration := average_duration_value; average_convexity := average_convexity_value; average_yld := average_yld_value; transmission_time := transmission_time_value; end_keyword := end_keyword_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 177.
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
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondPrimeIndexMessage.

  Module BondKtbIndexMessage.

    (** Bond KTB Index intraday calculation. Reports total profit, clean price, market price, call and zero re-investment indices, futures basis price, duration, convexity, and YTM for one KTB-based Bond Index ID. *)
    Record t := {
      bond_index_id : list byte;
      base_date : list byte;
      base_time : list byte;
      total_profit_index : list byte;
      clean_price_index_ktb : list byte;
      market_price_index_ktb : list byte;
      call_re_investment_index_ktb : list byte;
      zero_re_investment_index_ktb : list byte;
      futures_basis_price : list byte;
      duration : list byte;
      convexity : list byte;
      average_ytm : list byte;
      average_forward_ytm : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bond_index_id record) = 6 /\
      Datatypes.length (base_date record) = 8 /\
      Datatypes.length (base_time record) = 6 /\
      Datatypes.length (total_profit_index record) = 11 /\
      Datatypes.length (clean_price_index_ktb record) = 11 /\
      Datatypes.length (market_price_index_ktb record) = 11 /\
      Datatypes.length (call_re_investment_index_ktb record) = 11 /\
      Datatypes.length (zero_re_investment_index_ktb record) = 11 /\
      Datatypes.length (futures_basis_price record) = 10 /\
      Datatypes.length (duration record) = 7 /\
      Datatypes.length (convexity record) = 7 /\
      Datatypes.length (average_ytm record) = 7 /\
      Datatypes.length (average_forward_ytm record) = 7 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bond_index_id record) ++
      encode_bytes 8 (base_date record) ++
      encode_bytes 6 (base_time record) ++
      encode_bytes 11 (total_profit_index record) ++
      encode_bytes 11 (clean_price_index_ktb record) ++
      encode_bytes 11 (market_price_index_ktb record) ++
      encode_bytes 11 (call_re_investment_index_ktb record) ++
      encode_bytes 11 (zero_re_investment_index_ktb record) ++
      encode_bytes 10 (futures_basis_price record) ++
      encode_bytes 7 (duration record) ++
      encode_bytes 7 (convexity record) ++
      encode_bytes 7 (average_ytm record) ++
      encode_bytes 7 (average_forward_ytm record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bond_index_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (base_date_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (base_time_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (total_profit_index_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (clean_price_index_ktb_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (market_price_index_ktb_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (call_re_investment_index_ktb_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (zero_re_investment_index_ktb_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (futures_basis_price_value, bytes) =>
                                          match decode_bytes 7 bytes with
                                          | None => None
                                          | Some (duration_value, bytes) =>
                                              match decode_bytes 7 bytes with
                                              | None => None
                                              | Some (convexity_value, bytes) =>
                                                  match decode_bytes 7 bytes with
                                                  | None => None
                                                  | Some (average_ytm_value, bytes) =>
                                                      match decode_bytes 7 bytes with
                                                      | None => None
                                                      | Some (average_forward_ytm_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (end_keyword_value, bytes) =>
                                                              Some ({| bond_index_id := bond_index_id_value; base_date := base_date_value; base_time := base_time_value; total_profit_index := total_profit_index_value; clean_price_index_ktb := clean_price_index_ktb_value; market_price_index_ktb := market_price_index_ktb_value; call_re_investment_index_ktb := call_re_investment_index_ktb_value; zero_re_investment_index_ktb := zero_re_investment_index_ktb_value; futures_basis_price := futures_basis_price_value; duration := duration_value; convexity := convexity_value; average_ytm := average_ytm_value; average_forward_ytm := average_forward_ytm_value; end_keyword := end_keyword_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 114.
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
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondKtbIndexMessage.

  Module BondKtbIndexTermStructureMessage.

    (** Bond KTB Index TermStructure. One record per ISIN constituent of a KTB Index showing its basis price, clean price, YTM, and the Index Constituent flag. *)
    Record t := {
      bond_index_id : list byte;
      base_date : list byte;
      base_time : list byte;
      isin_code : list byte;
      basis_price : list byte;
      clean_price : list byte;
      average_ytm : list byte;
      index_constituent : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bond_index_id record) = 6 /\
      Datatypes.length (base_date record) = 8 /\
      Datatypes.length (base_time record) = 6 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (basis_price record) = 10 /\
      Datatypes.length (clean_price record) = 10 /\
      Datatypes.length (average_ytm record) = 7 /\
      Datatypes.length (index_constituent record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bond_index_id record) ++
      encode_bytes 8 (base_date record) ++
      encode_bytes 6 (base_time record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 10 (basis_price record) ++
      encode_bytes 10 (clean_price record) ++
      encode_bytes 7 (average_ytm record) ++
      encode_bytes 1 (index_constituent record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bond_index_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (base_date_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (base_time_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (basis_price_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (clean_price_value, bytes) =>
                              match decode_bytes 7 bytes with
                              | None => None
                              | Some (average_ytm_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (index_constituent_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (end_keyword_value, bytes) =>
                                          Some ({| bond_index_id := bond_index_id_value; base_date := base_date_value; base_time := base_time_value; isin_code := isin_code_value; basis_price := basis_price_value; clean_price := clean_price_value; average_ytm := average_ytm_value; index_constituent := index_constituent_value; end_keyword := end_keyword_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondKtbIndexTermStructureMessage.

  Module BondIndexKrxMessage.

    (** KRX Aggregate Bond Index (AA- or higher) end-of-day index data. Reports clean-price, total-earnings, market-price, and re-investment indices, their weighted variants, integrity-index weights, average duration, convexity, yield, coupon, remaining maturity, spread, market capitalization, and accumulated cash flows for one Bond Index ID. *)
    Record t := {
      message_sequence_number : list byte;
      calculating_date : list byte;
      index_id : list byte;
      clean_price_index_krx : list byte;
      total_earnings_index : list byte;
      market_price_index_krx : list byte;
      zero_re_investment_index_krx : list byte;
      call_re_investment_index_krx : list byte;
      clean_price_index_weight : list byte;
      total_earnings_index_weight : list byte;
      market_price_index_weight : list byte;
      zero_re_investment_index_weight : list byte;
      call_re_investment_index_weight : list byte;
      weight_of_clean_index_value_for_integrity_index_weight : list byte;
      weight_of_sum_index_value_for_integrity_index_weight : list byte;
      weight_of_zero_re_investment_index_value_for_integrity_index_weight : list byte;
      weight_of_call_re_investment_index_value_for_integrity_index_weight : list byte;
      average_duration : list byte;
      average_convexity : list byte;
      average_yld : list byte;
      average_coupon_price : list byte;
      average_remaining_maturity_price : list byte;
      average_current_yield : list byte;
      average_spread_sign : list byte;
      average_spread : list byte;
      index_number_of_securities : list byte;
      issued_amount : list byte;
      issued_amount_weight : list byte;
      index_market_capitalization : list byte;
      market_capitalization_weight : list byte;
      accumulated_cash : list byte;
      cash_inflow : list byte;
      reinvest_call_cash : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (calculating_date record) = 8 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (clean_price_index_krx record) = 16 /\
      Datatypes.length (total_earnings_index record) = 16 /\
      Datatypes.length (market_price_index_krx record) = 16 /\
      Datatypes.length (zero_re_investment_index_krx record) = 16 /\
      Datatypes.length (call_re_investment_index_krx record) = 16 /\
      Datatypes.length (clean_price_index_weight record) = 16 /\
      Datatypes.length (total_earnings_index_weight record) = 16 /\
      Datatypes.length (market_price_index_weight record) = 16 /\
      Datatypes.length (zero_re_investment_index_weight record) = 16 /\
      Datatypes.length (call_re_investment_index_weight record) = 16 /\
      Datatypes.length (weight_of_clean_index_value_for_integrity_index_weight record) = 16 /\
      Datatypes.length (weight_of_sum_index_value_for_integrity_index_weight record) = 16 /\
      Datatypes.length (weight_of_zero_re_investment_index_value_for_integrity_index_weight record) = 16 /\
      Datatypes.length (weight_of_call_re_investment_index_value_for_integrity_index_weight record) = 16 /\
      Datatypes.length (average_duration record) = 16 /\
      Datatypes.length (average_convexity record) = 16 /\
      Datatypes.length (average_yld record) = 16 /\
      Datatypes.length (average_coupon_price record) = 16 /\
      Datatypes.length (average_remaining_maturity_price record) = 16 /\
      Datatypes.length (average_current_yield record) = 16 /\
      Datatypes.length (average_spread_sign record) = 1 /\
      Datatypes.length (average_spread record) = 16 /\
      Datatypes.length (index_number_of_securities record) = 8 /\
      Datatypes.length (issued_amount record) = 20 /\
      Datatypes.length (issued_amount_weight record) = 16 /\
      Datatypes.length (index_market_capitalization record) = 20 /\
      Datatypes.length (market_capitalization_weight record) = 16 /\
      Datatypes.length (accumulated_cash record) = 26 /\
      Datatypes.length (cash_inflow record) = 26 /\
      Datatypes.length (reinvest_call_cash record) = 26 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 8 (calculating_date record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 16 (clean_price_index_krx record) ++
      encode_bytes 16 (total_earnings_index record) ++
      encode_bytes 16 (market_price_index_krx record) ++
      encode_bytes 16 (zero_re_investment_index_krx record) ++
      encode_bytes 16 (call_re_investment_index_krx record) ++
      encode_bytes 16 (clean_price_index_weight record) ++
      encode_bytes 16 (total_earnings_index_weight record) ++
      encode_bytes 16 (market_price_index_weight record) ++
      encode_bytes 16 (zero_re_investment_index_weight record) ++
      encode_bytes 16 (call_re_investment_index_weight record) ++
      encode_bytes 16 (weight_of_clean_index_value_for_integrity_index_weight record) ++
      encode_bytes 16 (weight_of_sum_index_value_for_integrity_index_weight record) ++
      encode_bytes 16 (weight_of_zero_re_investment_index_value_for_integrity_index_weight record) ++
      encode_bytes 16 (weight_of_call_re_investment_index_value_for_integrity_index_weight record) ++
      encode_bytes 16 (average_duration record) ++
      encode_bytes 16 (average_convexity record) ++
      encode_bytes 16 (average_yld record) ++
      encode_bytes 16 (average_coupon_price record) ++
      encode_bytes 16 (average_remaining_maturity_price record) ++
      encode_bytes 16 (average_current_yield record) ++
      encode_bytes 1 (average_spread_sign record) ++
      encode_bytes 16 (average_spread record) ++
      encode_bytes 8 (index_number_of_securities record) ++
      encode_bytes 20 (issued_amount record) ++
      encode_bytes 16 (issued_amount_weight record) ++
      encode_bytes 20 (index_market_capitalization record) ++
      encode_bytes 16 (market_capitalization_weight record) ++
      encode_bytes 26 (accumulated_cash record) ++
      encode_bytes 26 (cash_inflow record) ++
      encode_bytes 26 (reinvest_call_cash record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (calculating_date_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (index_id_value, bytes) =>
                  match decode_bytes 16 bytes with
                  | None => None
                  | Some (clean_price_index_krx_value, bytes) =>
                      match decode_bytes 16 bytes with
                      | None => None
                      | Some (total_earnings_index_value, bytes) =>
                          match decode_bytes 16 bytes with
                          | None => None
                          | Some (market_price_index_krx_value, bytes) =>
                              match decode_bytes 16 bytes with
                              | None => None
                              | Some (zero_re_investment_index_krx_value, bytes) =>
                                  match decode_bytes 16 bytes with
                                  | None => None
                                  | Some (call_re_investment_index_krx_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (clean_price_index_weight_value, bytes) =>
                                          match decode_bytes 16 bytes with
                                          | None => None
                                          | Some (total_earnings_index_weight_value, bytes) =>
                                              match decode_bytes 16 bytes with
                                              | None => None
                                              | Some (market_price_index_weight_value, bytes) =>
                                                  match decode_bytes 16 bytes with
                                                  | None => None
                                                  | Some (zero_re_investment_index_weight_value, bytes) =>
                                                      match decode_bytes 16 bytes with
                                                      | None => None
                                                      | Some (call_re_investment_index_weight_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (weight_of_clean_index_value_for_integrity_index_weight_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (weight_of_sum_index_value_for_integrity_index_weight_value, bytes) =>
                                                                  match decode_bytes 16 bytes with
                                                                  | None => None
                                                                  | Some (weight_of_zero_re_investment_index_value_for_integrity_index_weight_value, bytes) =>
                                                                      match decode_bytes 16 bytes with
                                                                      | None => None
                                                                      | Some (weight_of_call_re_investment_index_value_for_integrity_index_weight_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (average_duration_value, bytes) =>
                                                                              match decode_bytes 16 bytes with
                                                                              | None => None
                                                                              | Some (average_convexity_value, bytes) =>
                                                                                  match decode_bytes 16 bytes with
                                                                                  | None => None
                                                                                  | Some (average_yld_value, bytes) =>
                                                                                      match decode_bytes 16 bytes with
                                                                                      | None => None
                                                                                      | Some (average_coupon_price_value, bytes) =>
                                                                                          match decode_bytes 16 bytes with
                                                                                          | None => None
                                                                                          | Some (average_remaining_maturity_price_value, bytes) =>
                                                                                              match decode_bytes 16 bytes with
                                                                                              | None => None
                                                                                              | Some (average_current_yield_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (average_spread_sign_value, bytes) =>
                                                                                                      match decode_bytes 16 bytes with
                                                                                                      | None => None
                                                                                                      | Some (average_spread_value, bytes) =>
                                                                                                          match decode_bytes 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (index_number_of_securities_value, bytes) =>
                                                                                                              match decode_bytes 20 bytes with
                                                                                                              | None => None
                                                                                                              | Some (issued_amount_value, bytes) =>
                                                                                                                  match decode_bytes 16 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (issued_amount_weight_value, bytes) =>
                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (index_market_capitalization_value, bytes) =>
                                                                                                                          match decode_bytes 16 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (market_capitalization_weight_value, bytes) =>
                                                                                                                              match decode_bytes 26 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (accumulated_cash_value, bytes) =>
                                                                                                                                  match decode_bytes 26 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (cash_inflow_value, bytes) =>
                                                                                                                                      match decode_bytes 26 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (reinvest_call_cash_value, bytes) =>
                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; calculating_date := calculating_date_value; index_id := index_id_value; clean_price_index_krx := clean_price_index_krx_value; total_earnings_index := total_earnings_index_value; market_price_index_krx := market_price_index_krx_value; zero_re_investment_index_krx := zero_re_investment_index_krx_value; call_re_investment_index_krx := call_re_investment_index_krx_value; clean_price_index_weight := clean_price_index_weight_value; total_earnings_index_weight := total_earnings_index_weight_value; market_price_index_weight := market_price_index_weight_value; zero_re_investment_index_weight := zero_re_investment_index_weight_value; call_re_investment_index_weight := call_re_investment_index_weight_value; weight_of_clean_index_value_for_integrity_index_weight := weight_of_clean_index_value_for_integrity_index_weight_value; weight_of_sum_index_value_for_integrity_index_weight := weight_of_sum_index_value_for_integrity_index_weight_value; weight_of_zero_re_investment_index_value_for_integrity_index_weight := weight_of_zero_re_investment_index_value_for_integrity_index_weight_value; weight_of_call_re_investment_index_value_for_integrity_index_weight := weight_of_call_re_investment_index_value_for_integrity_index_weight_value; average_duration := average_duration_value; average_convexity := average_convexity_value; average_yld := average_yld_value; average_coupon_price := average_coupon_price_value; average_remaining_maturity_price := average_remaining_maturity_price_value; average_current_yield := average_current_yield_value; average_spread_sign := average_spread_sign_value; average_spread := average_spread_value; index_number_of_securities := index_number_of_securities_value; issued_amount := issued_amount_value; issued_amount_weight := issued_amount_weight_value; index_market_capitalization := index_market_capitalization_value; market_capitalization_weight := market_capitalization_weight_value; accumulated_cash := accumulated_cash_value; cash_inflow := cash_inflow_value; reinvest_call_cash := reinvest_call_cash_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 518.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 bound_33]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_33.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondIndexKrxMessage.

  Module SpotGoldQuoteMessage.

    (** Spot Gold Quote. Multi-level bid/ask quotes for Spot Gold. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      lp_ask_level_1_volume : list byte;
      lp_bid_level_1_volume : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      lp_ask_level_2_volume : list byte;
      lp_bid_level_2_volume : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      lp_ask_level_3_volume : list byte;
      lp_bid_level_3_volume : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      lp_ask_level_4_volume : list byte;
      lp_bid_level_4_volume : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      lp_ask_level_5_volume : list byte;
      lp_bid_level_5_volume : list byte;
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      lp_ask_level_6_volume : list byte;
      lp_bid_level_6_volume : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      lp_ask_level_7_volume : list byte;
      lp_bid_level_7_volume : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      lp_ask_level_8_volume : list byte;
      lp_bid_level_8_volume : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      lp_ask_level_9_volume : list byte;
      lp_bid_level_9_volume : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      lp_ask_level_10_volume : list byte;
      lp_bid_level_10_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_volume record) = 12 /\
      Datatypes.length (bid_level_1_volume record) = 12 /\
      Datatypes.length (lp_ask_level_1_volume record) = 12 /\
      Datatypes.length (lp_bid_level_1_volume record) = 12 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_volume record) = 12 /\
      Datatypes.length (bid_level_2_volume record) = 12 /\
      Datatypes.length (lp_ask_level_2_volume record) = 12 /\
      Datatypes.length (lp_bid_level_2_volume record) = 12 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_volume record) = 12 /\
      Datatypes.length (bid_level_3_volume record) = 12 /\
      Datatypes.length (lp_ask_level_3_volume record) = 12 /\
      Datatypes.length (lp_bid_level_3_volume record) = 12 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_volume record) = 12 /\
      Datatypes.length (bid_level_4_volume record) = 12 /\
      Datatypes.length (lp_ask_level_4_volume record) = 12 /\
      Datatypes.length (lp_bid_level_4_volume record) = 12 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_volume record) = 12 /\
      Datatypes.length (bid_level_5_volume record) = 12 /\
      Datatypes.length (lp_ask_level_5_volume record) = 12 /\
      Datatypes.length (lp_bid_level_5_volume record) = 12 /\
      Datatypes.length (ask_level_6_price record) = 11 /\
      Datatypes.length (bid_level_6_price record) = 11 /\
      Datatypes.length (ask_level_6_volume record) = 12 /\
      Datatypes.length (bid_level_6_volume record) = 12 /\
      Datatypes.length (lp_ask_level_6_volume record) = 12 /\
      Datatypes.length (lp_bid_level_6_volume record) = 12 /\
      Datatypes.length (ask_level_7_price record) = 11 /\
      Datatypes.length (bid_level_7_price record) = 11 /\
      Datatypes.length (ask_level_7_volume record) = 12 /\
      Datatypes.length (bid_level_7_volume record) = 12 /\
      Datatypes.length (lp_ask_level_7_volume record) = 12 /\
      Datatypes.length (lp_bid_level_7_volume record) = 12 /\
      Datatypes.length (ask_level_8_price record) = 11 /\
      Datatypes.length (bid_level_8_price record) = 11 /\
      Datatypes.length (ask_level_8_volume record) = 12 /\
      Datatypes.length (bid_level_8_volume record) = 12 /\
      Datatypes.length (lp_ask_level_8_volume record) = 12 /\
      Datatypes.length (lp_bid_level_8_volume record) = 12 /\
      Datatypes.length (ask_level_9_price record) = 11 /\
      Datatypes.length (bid_level_9_price record) = 11 /\
      Datatypes.length (ask_level_9_volume record) = 12 /\
      Datatypes.length (bid_level_9_volume record) = 12 /\
      Datatypes.length (lp_ask_level_9_volume record) = 12 /\
      Datatypes.length (lp_bid_level_9_volume record) = 12 /\
      Datatypes.length (ask_level_10_price record) = 11 /\
      Datatypes.length (bid_level_10_price record) = 11 /\
      Datatypes.length (ask_level_10_volume record) = 12 /\
      Datatypes.length (bid_level_10_volume record) = 12 /\
      Datatypes.length (lp_ask_level_10_volume record) = 12 /\
      Datatypes.length (lp_bid_level_10_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 12 (ask_level_1_volume record) ++
      encode_bytes 12 (bid_level_1_volume record) ++
      encode_bytes 12 (lp_ask_level_1_volume record) ++
      encode_bytes 12 (lp_bid_level_1_volume record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 12 (ask_level_2_volume record) ++
      encode_bytes 12 (bid_level_2_volume record) ++
      encode_bytes 12 (lp_ask_level_2_volume record) ++
      encode_bytes 12 (lp_bid_level_2_volume record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 12 (ask_level_3_volume record) ++
      encode_bytes 12 (bid_level_3_volume record) ++
      encode_bytes 12 (lp_ask_level_3_volume record) ++
      encode_bytes 12 (lp_bid_level_3_volume record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 12 (ask_level_4_volume record) ++
      encode_bytes 12 (bid_level_4_volume record) ++
      encode_bytes 12 (lp_ask_level_4_volume record) ++
      encode_bytes 12 (lp_bid_level_4_volume record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 12 (ask_level_5_volume record) ++
      encode_bytes 12 (bid_level_5_volume record) ++
      encode_bytes 12 (lp_ask_level_5_volume record) ++
      encode_bytes 12 (lp_bid_level_5_volume record) ++
      encode_bytes 11 (ask_level_6_price record) ++
      encode_bytes 11 (bid_level_6_price record) ++
      encode_bytes 12 (ask_level_6_volume record) ++
      encode_bytes 12 (bid_level_6_volume record) ++
      encode_bytes 12 (lp_ask_level_6_volume record) ++
      encode_bytes 12 (lp_bid_level_6_volume record) ++
      encode_bytes 11 (ask_level_7_price record) ++
      encode_bytes 11 (bid_level_7_price record) ++
      encode_bytes 12 (ask_level_7_volume record) ++
      encode_bytes 12 (bid_level_7_volume record) ++
      encode_bytes 12 (lp_ask_level_7_volume record) ++
      encode_bytes 12 (lp_bid_level_7_volume record) ++
      encode_bytes 11 (ask_level_8_price record) ++
      encode_bytes 11 (bid_level_8_price record) ++
      encode_bytes 12 (ask_level_8_volume record) ++
      encode_bytes 12 (bid_level_8_volume record) ++
      encode_bytes 12 (lp_ask_level_8_volume record) ++
      encode_bytes 12 (lp_bid_level_8_volume record) ++
      encode_bytes 11 (ask_level_9_price record) ++
      encode_bytes 11 (bid_level_9_price record) ++
      encode_bytes 12 (ask_level_9_volume record) ++
      encode_bytes 12 (bid_level_9_volume record) ++
      encode_bytes 12 (lp_ask_level_9_volume record) ++
      encode_bytes 12 (lp_bid_level_9_volume record) ++
      encode_bytes 11 (ask_level_10_price record) ++
      encode_bytes 11 (bid_level_10_price record) ++
      encode_bytes 12 (ask_level_10_volume record) ++
      encode_bytes 12 (bid_level_10_volume record) ++
      encode_bytes 12 (lp_ask_level_10_volume record) ++
      encode_bytes 12 (lp_bid_level_10_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (ask_level_1_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (bid_level_1_price_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (ask_level_1_volume_value, bytes) =>
                                          match decode_bytes 12 bytes with
                                          | None => None
                                          | Some (bid_level_1_volume_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (lp_ask_level_1_volume_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (lp_bid_level_1_volume_value, bytes) =>
                                                      match decode_bytes 11 bytes with
                                                      | None => None
                                                      | Some (ask_level_2_price_value, bytes) =>
                                                          match decode_bytes 11 bytes with
                                                          | None => None
                                                          | Some (bid_level_2_price_value, bytes) =>
                                                              match decode_bytes 12 bytes with
                                                              | None => None
                                                              | Some (ask_level_2_volume_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (bid_level_2_volume_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (lp_ask_level_2_volume_value, bytes) =>
                                                                          match decode_bytes 12 bytes with
                                                                          | None => None
                                                                          | Some (lp_bid_level_2_volume_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_3_price_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_3_price_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_level_3_volume_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_level_3_volume_value, bytes) =>
                                                                                              match decode_bytes 12 bytes with
                                                                                              | None => None
                                                                                              | Some (lp_ask_level_3_volume_value, bytes) =>
                                                                                                  match decode_bytes 12 bytes with
                                                                                                  | None => None
                                                                                                  | Some (lp_bid_level_3_volume_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_4_price_value, bytes) =>
                                                                                                          match decode_bytes 11 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_4_price_value, bytes) =>
                                                                                                              match decode_bytes 12 bytes with
                                                                                                              | None => None
                                                                                                              | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (lp_ask_level_4_volume_value, bytes) =>
                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (lp_bid_level_4_volume_value, bytes) =>
                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (lp_ask_level_5_volume_value, bytes) =>
                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (lp_bid_level_5_volume_value, bytes) =>
                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_level_6_price_value, bytes) =>
                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_level_6_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ask_level_6_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (bid_level_6_volume_value, bytes) =>
                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (lp_ask_level_6_volume_value, bytes) =>
                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (lp_bid_level_6_volume_value, bytes) =>
                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (ask_level_7_price_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (bid_level_7_price_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (lp_ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (lp_bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (ask_level_8_price_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (lp_ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (lp_bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (ask_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (lp_ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (lp_bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (ask_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (lp_ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (lp_bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (total_ask_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (total_bid_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; lp_ask_level_1_volume := lp_ask_level_1_volume_value; lp_bid_level_1_volume := lp_bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; lp_ask_level_2_volume := lp_ask_level_2_volume_value; lp_bid_level_2_volume := lp_bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; lp_ask_level_3_volume := lp_ask_level_3_volume_value; lp_bid_level_3_volume := lp_bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; lp_ask_level_4_volume := lp_ask_level_4_volume_value; lp_bid_level_4_volume := lp_bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; lp_ask_level_5_volume := lp_ask_level_5_volume_value; lp_bid_level_5_volume := lp_bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; lp_ask_level_6_volume := lp_ask_level_6_volume_value; lp_bid_level_6_volume := lp_bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; lp_ask_level_7_volume := lp_ask_level_7_volume_value; lp_bid_level_7_volume := lp_bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; lp_ask_level_8_volume := lp_ask_level_8_volume_value; lp_bid_level_8_volume := lp_bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; lp_ask_level_9_volume := lp_ask_level_9_volume_value; lp_bid_level_9_volume := lp_bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; lp_ask_level_10_volume := lp_ask_level_10_volume_value; lp_bid_level_10_volume := lp_bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 790.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 bound_70]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_45.
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
      rewrite decode_encode_uint by exact bound_70.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldQuoteMessage.

  Module SpotGoldOrderFilledMessage.

    (** Spot Gold Order Filled. Real-time trade prints with running totals. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      previous_price : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      lp_holding_quantity : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (previous_price record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (lp_holding_quantity record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 11 (previous_price record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 15 (lp_holding_quantity record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (trading_volume_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (opening_price_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (todays_high_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (todays_low_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (previous_price_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (accumulated_trading_volume_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_value_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (final_ask_bid_type_code_value, bytes) =>
                                                                  match decode_bytes 15 bytes with
                                                                  | None => None
                                                                  | Some (lp_holding_quantity_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (end_keyword_value, bytes) =>
                                                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; previous_price := previous_price_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; lp_holding_quantity := lp_holding_quantity_value; end_keyword := end_keyword_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 156.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldOrderFilledMessage.

  Module SpotGoldOrderFilledPlusQuoteMessage.

    (** Spot Gold Order Filled plus Quote. Trade print followed by full quote state. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      previous_price : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      lp_holding_quantity : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      lp_ask_level_1_volume : list byte;
      lp_bid_level_1_volume : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      lp_ask_level_2_volume : list byte;
      lp_bid_level_2_volume : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      lp_ask_level_3_volume : list byte;
      lp_bid_level_3_volume : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      lp_ask_level_4_volume : list byte;
      lp_bid_level_4_volume : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      lp_ask_level_5_volume : list byte;
      lp_bid_level_5_volume : list byte;
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      lp_ask_level_6_volume : list byte;
      lp_bid_level_6_volume : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      lp_ask_level_7_volume : list byte;
      lp_bid_level_7_volume : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      lp_ask_level_8_volume : list byte;
      lp_bid_level_8_volume : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      lp_ask_level_9_volume : list byte;
      lp_bid_level_9_volume : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      lp_ask_level_10_volume : list byte;
      lp_bid_level_10_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (previous_price record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (lp_holding_quantity record) = 15 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_volume record) = 12 /\
      Datatypes.length (bid_level_1_volume record) = 12 /\
      Datatypes.length (lp_ask_level_1_volume record) = 12 /\
      Datatypes.length (lp_bid_level_1_volume record) = 12 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_volume record) = 12 /\
      Datatypes.length (bid_level_2_volume record) = 12 /\
      Datatypes.length (lp_ask_level_2_volume record) = 12 /\
      Datatypes.length (lp_bid_level_2_volume record) = 12 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_volume record) = 12 /\
      Datatypes.length (bid_level_3_volume record) = 12 /\
      Datatypes.length (lp_ask_level_3_volume record) = 12 /\
      Datatypes.length (lp_bid_level_3_volume record) = 12 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_volume record) = 12 /\
      Datatypes.length (bid_level_4_volume record) = 12 /\
      Datatypes.length (lp_ask_level_4_volume record) = 12 /\
      Datatypes.length (lp_bid_level_4_volume record) = 12 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_volume record) = 12 /\
      Datatypes.length (bid_level_5_volume record) = 12 /\
      Datatypes.length (lp_ask_level_5_volume record) = 12 /\
      Datatypes.length (lp_bid_level_5_volume record) = 12 /\
      Datatypes.length (ask_level_6_price record) = 11 /\
      Datatypes.length (bid_level_6_price record) = 11 /\
      Datatypes.length (ask_level_6_volume record) = 12 /\
      Datatypes.length (bid_level_6_volume record) = 12 /\
      Datatypes.length (lp_ask_level_6_volume record) = 12 /\
      Datatypes.length (lp_bid_level_6_volume record) = 12 /\
      Datatypes.length (ask_level_7_price record) = 11 /\
      Datatypes.length (bid_level_7_price record) = 11 /\
      Datatypes.length (ask_level_7_volume record) = 12 /\
      Datatypes.length (bid_level_7_volume record) = 12 /\
      Datatypes.length (lp_ask_level_7_volume record) = 12 /\
      Datatypes.length (lp_bid_level_7_volume record) = 12 /\
      Datatypes.length (ask_level_8_price record) = 11 /\
      Datatypes.length (bid_level_8_price record) = 11 /\
      Datatypes.length (ask_level_8_volume record) = 12 /\
      Datatypes.length (bid_level_8_volume record) = 12 /\
      Datatypes.length (lp_ask_level_8_volume record) = 12 /\
      Datatypes.length (lp_bid_level_8_volume record) = 12 /\
      Datatypes.length (ask_level_9_price record) = 11 /\
      Datatypes.length (bid_level_9_price record) = 11 /\
      Datatypes.length (ask_level_9_volume record) = 12 /\
      Datatypes.length (bid_level_9_volume record) = 12 /\
      Datatypes.length (lp_ask_level_9_volume record) = 12 /\
      Datatypes.length (lp_bid_level_9_volume record) = 12 /\
      Datatypes.length (ask_level_10_price record) = 11 /\
      Datatypes.length (bid_level_10_price record) = 11 /\
      Datatypes.length (ask_level_10_volume record) = 12 /\
      Datatypes.length (bid_level_10_volume record) = 12 /\
      Datatypes.length (lp_ask_level_10_volume record) = 12 /\
      Datatypes.length (lp_bid_level_10_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 11 (previous_price record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 15 (lp_holding_quantity record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 12 (ask_level_1_volume record) ++
      encode_bytes 12 (bid_level_1_volume record) ++
      encode_bytes 12 (lp_ask_level_1_volume record) ++
      encode_bytes 12 (lp_bid_level_1_volume record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 12 (ask_level_2_volume record) ++
      encode_bytes 12 (bid_level_2_volume record) ++
      encode_bytes 12 (lp_ask_level_2_volume record) ++
      encode_bytes 12 (lp_bid_level_2_volume record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 12 (ask_level_3_volume record) ++
      encode_bytes 12 (bid_level_3_volume record) ++
      encode_bytes 12 (lp_ask_level_3_volume record) ++
      encode_bytes 12 (lp_bid_level_3_volume record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 12 (ask_level_4_volume record) ++
      encode_bytes 12 (bid_level_4_volume record) ++
      encode_bytes 12 (lp_ask_level_4_volume record) ++
      encode_bytes 12 (lp_bid_level_4_volume record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 12 (ask_level_5_volume record) ++
      encode_bytes 12 (bid_level_5_volume record) ++
      encode_bytes 12 (lp_ask_level_5_volume record) ++
      encode_bytes 12 (lp_bid_level_5_volume record) ++
      encode_bytes 11 (ask_level_6_price record) ++
      encode_bytes 11 (bid_level_6_price record) ++
      encode_bytes 12 (ask_level_6_volume record) ++
      encode_bytes 12 (bid_level_6_volume record) ++
      encode_bytes 12 (lp_ask_level_6_volume record) ++
      encode_bytes 12 (lp_bid_level_6_volume record) ++
      encode_bytes 11 (ask_level_7_price record) ++
      encode_bytes 11 (bid_level_7_price record) ++
      encode_bytes 12 (ask_level_7_volume record) ++
      encode_bytes 12 (bid_level_7_volume record) ++
      encode_bytes 12 (lp_ask_level_7_volume record) ++
      encode_bytes 12 (lp_bid_level_7_volume record) ++
      encode_bytes 11 (ask_level_8_price record) ++
      encode_bytes 11 (bid_level_8_price record) ++
      encode_bytes 12 (ask_level_8_volume record) ++
      encode_bytes 12 (bid_level_8_volume record) ++
      encode_bytes 12 (lp_ask_level_8_volume record) ++
      encode_bytes 12 (lp_bid_level_8_volume record) ++
      encode_bytes 11 (ask_level_9_price record) ++
      encode_bytes 11 (bid_level_9_price record) ++
      encode_bytes 12 (ask_level_9_volume record) ++
      encode_bytes 12 (bid_level_9_volume record) ++
      encode_bytes 12 (lp_ask_level_9_volume record) ++
      encode_bytes 12 (lp_bid_level_9_volume record) ++
      encode_bytes 11 (ask_level_10_price record) ++
      encode_bytes 11 (bid_level_10_price record) ++
      encode_bytes 12 (ask_level_10_volume record) ++
      encode_bytes 12 (bid_level_10_volume record) ++
      encode_bytes 12 (lp_ask_level_10_volume record) ++
      encode_bytes 12 (lp_bid_level_10_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (trading_volume_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (opening_price_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (todays_high_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (todays_low_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (previous_price_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (accumulated_trading_volume_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_value_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (final_ask_bid_type_code_value, bytes) =>
                                                                  match decode_bytes 15 bytes with
                                                                  | None => None
                                                                  | Some (lp_holding_quantity_value, bytes) =>
                                                                      match decode_bytes 11 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_1_price_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_1_price_value, bytes) =>
                                                                              match decode_bytes 12 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_1_volume_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_1_volume_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (lp_ask_level_1_volume_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (lp_bid_level_1_volume_value, bytes) =>
                                                                                              match decode_bytes 11 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_level_2_price_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_level_2_price_value, bytes) =>
                                                                                                      match decode_bytes 12 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_2_volume_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_2_volume_value, bytes) =>
                                                                                                              match decode_bytes 12 bytes with
                                                                                                              | None => None
                                                                                                              | Some (lp_ask_level_2_volume_value, bytes) =>
                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (lp_bid_level_2_volume_value, bytes) =>
                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_level_3_price_value, bytes) =>
                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_level_3_price_value, bytes) =>
                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (ask_level_3_volume_value, bytes) =>
                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (lp_ask_level_3_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (lp_bid_level_3_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (lp_ask_level_4_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (lp_bid_level_4_volume_value, bytes) =>
                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (lp_ask_level_5_volume_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (lp_bid_level_5_volume_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (ask_level_6_price_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (bid_level_6_price_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (lp_ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (lp_bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (ask_level_7_price_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (bid_level_7_price_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (lp_ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (lp_bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (ask_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (lp_ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (lp_bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (ask_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (lp_ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (lp_bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (ask_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (lp_ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (lp_bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (total_ask_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (total_bid_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; previous_price := previous_price_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; lp_holding_quantity := lp_holding_quantity_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; lp_ask_level_1_volume := lp_ask_level_1_volume_value; lp_bid_level_1_volume := lp_bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; lp_ask_level_2_volume := lp_ask_level_2_volume_value; lp_bid_level_2_volume := lp_bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; lp_ask_level_3_volume := lp_ask_level_3_volume_value; lp_bid_level_3_volume := lp_bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; lp_ask_level_4_volume := lp_ask_level_4_volume_value; lp_bid_level_4_volume := lp_bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; lp_ask_level_5_volume := lp_ask_level_5_volume_value; lp_bid_level_5_volume := lp_bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; lp_ask_level_6_volume := lp_ask_level_6_volume_value; lp_bid_level_6_volume := lp_bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; lp_ask_level_7_volume := lp_ask_level_7_volume_value; lp_bid_level_7_volume := lp_bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; lp_ask_level_8_volume := lp_ask_level_8_volume_value; lp_bid_level_8_volume := lp_bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; lp_ask_level_9_volume := lp_ask_level_9_volume_value; lp_bid_level_9_volume := lp_bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; lp_ask_level_10_volume := lp_ask_level_10_volume_value; lp_bid_level_10_volume := lp_bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 880.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 bound_78]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_45.
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
      rewrite decode_encode_uint by exact bound_78.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldOrderFilledPlusQuoteMessage.

  Module SpotGoldMarketOperationTsPlusQuoteMessage.

    (** Spot Gold Market Operation TS plus Quote. Session-state event followed by full quote state. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : list byte;
      trading_halt_reason_code : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      lp_ask_level_1_volume : list byte;
      lp_bid_level_1_volume : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      lp_ask_level_2_volume : list byte;
      lp_bid_level_2_volume : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      lp_ask_level_3_volume : list byte;
      lp_bid_level_3_volume : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      lp_ask_level_4_volume : list byte;
      lp_bid_level_4_volume : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      lp_ask_level_5_volume : list byte;
      lp_bid_level_5_volume : list byte;
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      lp_ask_level_6_volume : list byte;
      lp_bid_level_6_volume : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      lp_ask_level_7_volume : list byte;
      lp_bid_level_7_volume : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      lp_ask_level_8_volume : list byte;
      lp_bid_level_8_volume : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      lp_ask_level_9_volume : list byte;
      lp_bid_level_9_volume : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      lp_ask_level_10_volume : list byte;
      lp_bid_level_10_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      Datatypes.length (board_event_group_code record) = 5 /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_volume record) = 12 /\
      Datatypes.length (bid_level_1_volume record) = 12 /\
      Datatypes.length (lp_ask_level_1_volume record) = 12 /\
      Datatypes.length (lp_bid_level_1_volume record) = 12 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_volume record) = 12 /\
      Datatypes.length (bid_level_2_volume record) = 12 /\
      Datatypes.length (lp_ask_level_2_volume record) = 12 /\
      Datatypes.length (lp_bid_level_2_volume record) = 12 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_volume record) = 12 /\
      Datatypes.length (bid_level_3_volume record) = 12 /\
      Datatypes.length (lp_ask_level_3_volume record) = 12 /\
      Datatypes.length (lp_bid_level_3_volume record) = 12 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_volume record) = 12 /\
      Datatypes.length (bid_level_4_volume record) = 12 /\
      Datatypes.length (lp_ask_level_4_volume record) = 12 /\
      Datatypes.length (lp_bid_level_4_volume record) = 12 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_volume record) = 12 /\
      Datatypes.length (bid_level_5_volume record) = 12 /\
      Datatypes.length (lp_ask_level_5_volume record) = 12 /\
      Datatypes.length (lp_bid_level_5_volume record) = 12 /\
      Datatypes.length (ask_level_6_price record) = 11 /\
      Datatypes.length (bid_level_6_price record) = 11 /\
      Datatypes.length (ask_level_6_volume record) = 12 /\
      Datatypes.length (bid_level_6_volume record) = 12 /\
      Datatypes.length (lp_ask_level_6_volume record) = 12 /\
      Datatypes.length (lp_bid_level_6_volume record) = 12 /\
      Datatypes.length (ask_level_7_price record) = 11 /\
      Datatypes.length (bid_level_7_price record) = 11 /\
      Datatypes.length (ask_level_7_volume record) = 12 /\
      Datatypes.length (bid_level_7_volume record) = 12 /\
      Datatypes.length (lp_ask_level_7_volume record) = 12 /\
      Datatypes.length (lp_bid_level_7_volume record) = 12 /\
      Datatypes.length (ask_level_8_price record) = 11 /\
      Datatypes.length (bid_level_8_price record) = 11 /\
      Datatypes.length (ask_level_8_volume record) = 12 /\
      Datatypes.length (bid_level_8_volume record) = 12 /\
      Datatypes.length (lp_ask_level_8_volume record) = 12 /\
      Datatypes.length (lp_bid_level_8_volume record) = 12 /\
      Datatypes.length (ask_level_9_price record) = 11 /\
      Datatypes.length (bid_level_9_price record) = 11 /\
      Datatypes.length (ask_level_9_volume record) = 12 /\
      Datatypes.length (bid_level_9_volume record) = 12 /\
      Datatypes.length (lp_ask_level_9_volume record) = 12 /\
      Datatypes.length (lp_bid_level_9_volume record) = 12 /\
      Datatypes.length (ask_level_10_price record) = 11 /\
      Datatypes.length (bid_level_10_price record) = 11 /\
      Datatypes.length (ask_level_10_volume record) = 12 /\
      Datatypes.length (bid_level_10_volume record) = 12 /\
      Datatypes.length (lp_ask_level_10_volume record) = 12 /\
      Datatypes.length (lp_bid_level_10_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_bytes 5 (board_event_group_code record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 12 (ask_level_1_volume record) ++
      encode_bytes 12 (bid_level_1_volume record) ++
      encode_bytes 12 (lp_ask_level_1_volume record) ++
      encode_bytes 12 (lp_bid_level_1_volume record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 12 (ask_level_2_volume record) ++
      encode_bytes 12 (bid_level_2_volume record) ++
      encode_bytes 12 (lp_ask_level_2_volume record) ++
      encode_bytes 12 (lp_bid_level_2_volume record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 12 (ask_level_3_volume record) ++
      encode_bytes 12 (bid_level_3_volume record) ++
      encode_bytes 12 (lp_ask_level_3_volume record) ++
      encode_bytes 12 (lp_bid_level_3_volume record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 12 (ask_level_4_volume record) ++
      encode_bytes 12 (bid_level_4_volume record) ++
      encode_bytes 12 (lp_ask_level_4_volume record) ++
      encode_bytes 12 (lp_bid_level_4_volume record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 12 (ask_level_5_volume record) ++
      encode_bytes 12 (bid_level_5_volume record) ++
      encode_bytes 12 (lp_ask_level_5_volume record) ++
      encode_bytes 12 (lp_bid_level_5_volume record) ++
      encode_bytes 11 (ask_level_6_price record) ++
      encode_bytes 11 (bid_level_6_price record) ++
      encode_bytes 12 (ask_level_6_volume record) ++
      encode_bytes 12 (bid_level_6_volume record) ++
      encode_bytes 12 (lp_ask_level_6_volume record) ++
      encode_bytes 12 (lp_bid_level_6_volume record) ++
      encode_bytes 11 (ask_level_7_price record) ++
      encode_bytes 11 (bid_level_7_price record) ++
      encode_bytes 12 (ask_level_7_volume record) ++
      encode_bytes 12 (bid_level_7_volume record) ++
      encode_bytes 12 (lp_ask_level_7_volume record) ++
      encode_bytes 12 (lp_bid_level_7_volume record) ++
      encode_bytes 11 (ask_level_8_price record) ++
      encode_bytes 11 (bid_level_8_price record) ++
      encode_bytes 12 (ask_level_8_volume record) ++
      encode_bytes 12 (bid_level_8_volume record) ++
      encode_bytes 12 (lp_ask_level_8_volume record) ++
      encode_bytes 12 (lp_bid_level_8_volume record) ++
      encode_bytes 11 (ask_level_9_price record) ++
      encode_bytes 11 (bid_level_9_price record) ++
      encode_bytes 12 (ask_level_9_volume record) ++
      encode_bytes 12 (bid_level_9_volume record) ++
      encode_bytes 12 (lp_ask_level_9_volume record) ++
      encode_bytes 12 (lp_bid_level_9_volume record) ++
      encode_bytes 11 (ask_level_10_price record) ++
      encode_bytes 11 (bid_level_10_price record) ++
      encode_bytes 12 (ask_level_10_volume record) ++
      encode_bytes 12 (bid_level_10_volume record) ++
      encode_bytes 12 (lp_ask_level_10_volume record) ++
      encode_bytes 12 (lp_bid_level_10_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (board_event_id_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (start_time_of_a_board_event_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (board_event_group_code_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (trading_halt_reason_code_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (ask_level_1_price_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (bid_level_1_price_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (ask_level_1_volume_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (bid_level_1_volume_value, bytes) =>
                                                              match decode_bytes 12 bytes with
                                                              | None => None
                                                              | Some (lp_ask_level_1_volume_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (lp_bid_level_1_volume_value, bytes) =>
                                                                      match decode_bytes 11 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_2_price_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_2_price_value, bytes) =>
                                                                              match decode_bytes 12 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_2_volume_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_2_volume_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (lp_ask_level_2_volume_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (lp_bid_level_2_volume_value, bytes) =>
                                                                                              match decode_bytes 11 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_level_3_price_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_level_3_price_value, bytes) =>
                                                                                                      match decode_bytes 12 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_3_volume_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_3_volume_value, bytes) =>
                                                                                                              match decode_bytes 12 bytes with
                                                                                                              | None => None
                                                                                                              | Some (lp_ask_level_3_volume_value, bytes) =>
                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (lp_bid_level_3_volume_value, bytes) =>
                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_level_4_price_value, bytes) =>
                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_level_4_price_value, bytes) =>
                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (lp_ask_level_4_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (lp_bid_level_4_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (lp_ask_level_5_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (lp_bid_level_5_volume_value, bytes) =>
                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_level_6_price_value, bytes) =>
                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (bid_level_6_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (lp_ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (lp_bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (ask_level_7_price_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (bid_level_7_price_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (lp_ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (lp_bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (ask_level_8_price_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (lp_ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (lp_bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (ask_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (lp_ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (lp_bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (ask_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (lp_ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (lp_bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (total_ask_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (total_bid_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; trading_halt_reason_code := trading_halt_reason_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; lp_ask_level_1_volume := lp_ask_level_1_volume_value; lp_bid_level_1_volume := lp_bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; lp_ask_level_2_volume := lp_ask_level_2_volume_value; lp_bid_level_2_volume := lp_bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; lp_ask_level_3_volume := lp_ask_level_3_volume_value; lp_bid_level_3_volume := lp_bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; lp_ask_level_4_volume := lp_ask_level_4_volume_value; lp_bid_level_4_volume := lp_bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; lp_ask_level_5_volume := lp_ask_level_5_volume_value; lp_bid_level_5_volume := lp_bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; lp_ask_level_6_volume := lp_ask_level_6_volume_value; lp_bid_level_6_volume := lp_bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; lp_ask_level_7_volume := lp_ask_level_7_volume_value; lp_bid_level_7_volume := lp_bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; lp_ask_level_8_volume := lp_ask_level_8_volume_value; lp_bid_level_8_volume := lp_bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; lp_ask_level_9_volume := lp_ask_level_9_volume_value; lp_bid_level_9_volume := lp_bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; lp_ask_level_10_volume := lp_ask_level_10_volume_value; lp_bid_level_10_volume := lp_bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 810.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 bound_74]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_45.
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
      rewrite decode_encode_uint by exact bound_74.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldMarketOperationTsPlusQuoteMessage.

  Module SpotGoldSnapshotMessage.

    (** Spot Gold Market Data Snapshot. Periodic full state snapshot. *)
    Record t := {
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      current_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      trading_halt : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      lp_ask_level_1_volume : list byte;
      lp_bid_level_1_volume : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      lp_ask_level_2_volume : list byte;
      lp_bid_level_2_volume : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      lp_ask_level_3_volume : list byte;
      lp_bid_level_3_volume : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      lp_ask_level_4_volume : list byte;
      lp_bid_level_4_volume : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      lp_ask_level_5_volume : list byte;
      lp_bid_level_5_volume : list byte;
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      lp_ask_level_6_volume : list byte;
      lp_bid_level_6_volume : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      lp_ask_level_7_volume : list byte;
      lp_bid_level_7_volume : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      lp_ask_level_8_volume : list byte;
      lp_bid_level_8_volume : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      lp_ask_level_9_volume : list byte;
      lp_bid_level_9_volume : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      lp_ask_level_10_volume : list byte;
      lp_bid_level_10_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (current_price record) = 11 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_volume record) = 12 /\
      Datatypes.length (bid_level_1_volume record) = 12 /\
      Datatypes.length (lp_ask_level_1_volume record) = 12 /\
      Datatypes.length (lp_bid_level_1_volume record) = 12 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_volume record) = 12 /\
      Datatypes.length (bid_level_2_volume record) = 12 /\
      Datatypes.length (lp_ask_level_2_volume record) = 12 /\
      Datatypes.length (lp_bid_level_2_volume record) = 12 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_volume record) = 12 /\
      Datatypes.length (bid_level_3_volume record) = 12 /\
      Datatypes.length (lp_ask_level_3_volume record) = 12 /\
      Datatypes.length (lp_bid_level_3_volume record) = 12 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_volume record) = 12 /\
      Datatypes.length (bid_level_4_volume record) = 12 /\
      Datatypes.length (lp_ask_level_4_volume record) = 12 /\
      Datatypes.length (lp_bid_level_4_volume record) = 12 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_volume record) = 12 /\
      Datatypes.length (bid_level_5_volume record) = 12 /\
      Datatypes.length (lp_ask_level_5_volume record) = 12 /\
      Datatypes.length (lp_bid_level_5_volume record) = 12 /\
      Datatypes.length (ask_level_6_price record) = 11 /\
      Datatypes.length (bid_level_6_price record) = 11 /\
      Datatypes.length (ask_level_6_volume record) = 12 /\
      Datatypes.length (bid_level_6_volume record) = 12 /\
      Datatypes.length (lp_ask_level_6_volume record) = 12 /\
      Datatypes.length (lp_bid_level_6_volume record) = 12 /\
      Datatypes.length (ask_level_7_price record) = 11 /\
      Datatypes.length (bid_level_7_price record) = 11 /\
      Datatypes.length (ask_level_7_volume record) = 12 /\
      Datatypes.length (bid_level_7_volume record) = 12 /\
      Datatypes.length (lp_ask_level_7_volume record) = 12 /\
      Datatypes.length (lp_bid_level_7_volume record) = 12 /\
      Datatypes.length (ask_level_8_price record) = 11 /\
      Datatypes.length (bid_level_8_price record) = 11 /\
      Datatypes.length (ask_level_8_volume record) = 12 /\
      Datatypes.length (bid_level_8_volume record) = 12 /\
      Datatypes.length (lp_ask_level_8_volume record) = 12 /\
      Datatypes.length (lp_bid_level_8_volume record) = 12 /\
      Datatypes.length (ask_level_9_price record) = 11 /\
      Datatypes.length (bid_level_9_price record) = 11 /\
      Datatypes.length (ask_level_9_volume record) = 12 /\
      Datatypes.length (bid_level_9_volume record) = 12 /\
      Datatypes.length (lp_ask_level_9_volume record) = 12 /\
      Datatypes.length (lp_bid_level_9_volume record) = 12 /\
      Datatypes.length (ask_level_10_price record) = 11 /\
      Datatypes.length (bid_level_10_price record) = 11 /\
      Datatypes.length (ask_level_10_volume record) = 12 /\
      Datatypes.length (bid_level_10_volume record) = 12 /\
      Datatypes.length (lp_ask_level_10_volume record) = 12 /\
      Datatypes.length (lp_bid_level_10_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 11 (current_price record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 12 (ask_level_1_volume record) ++
      encode_bytes 12 (bid_level_1_volume record) ++
      encode_bytes 12 (lp_ask_level_1_volume record) ++
      encode_bytes 12 (lp_bid_level_1_volume record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 12 (ask_level_2_volume record) ++
      encode_bytes 12 (bid_level_2_volume record) ++
      encode_bytes 12 (lp_ask_level_2_volume record) ++
      encode_bytes 12 (lp_bid_level_2_volume record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 12 (ask_level_3_volume record) ++
      encode_bytes 12 (bid_level_3_volume record) ++
      encode_bytes 12 (lp_ask_level_3_volume record) ++
      encode_bytes 12 (lp_bid_level_3_volume record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 12 (ask_level_4_volume record) ++
      encode_bytes 12 (bid_level_4_volume record) ++
      encode_bytes 12 (lp_ask_level_4_volume record) ++
      encode_bytes 12 (lp_bid_level_4_volume record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 12 (ask_level_5_volume record) ++
      encode_bytes 12 (bid_level_5_volume record) ++
      encode_bytes 12 (lp_ask_level_5_volume record) ++
      encode_bytes 12 (lp_bid_level_5_volume record) ++
      encode_bytes 11 (ask_level_6_price record) ++
      encode_bytes 11 (bid_level_6_price record) ++
      encode_bytes 12 (ask_level_6_volume record) ++
      encode_bytes 12 (bid_level_6_volume record) ++
      encode_bytes 12 (lp_ask_level_6_volume record) ++
      encode_bytes 12 (lp_bid_level_6_volume record) ++
      encode_bytes 11 (ask_level_7_price record) ++
      encode_bytes 11 (bid_level_7_price record) ++
      encode_bytes 12 (ask_level_7_volume record) ++
      encode_bytes 12 (bid_level_7_volume record) ++
      encode_bytes 12 (lp_ask_level_7_volume record) ++
      encode_bytes 12 (lp_bid_level_7_volume record) ++
      encode_bytes 11 (ask_level_8_price record) ++
      encode_bytes 11 (bid_level_8_price record) ++
      encode_bytes 12 (ask_level_8_volume record) ++
      encode_bytes 12 (bid_level_8_volume record) ++
      encode_bytes 12 (lp_ask_level_8_volume record) ++
      encode_bytes 12 (lp_bid_level_8_volume record) ++
      encode_bytes 11 (ask_level_9_price record) ++
      encode_bytes 11 (bid_level_9_price record) ++
      encode_bytes 12 (ask_level_9_volume record) ++
      encode_bytes 12 (bid_level_9_volume record) ++
      encode_bytes 12 (lp_ask_level_9_volume record) ++
      encode_bytes 12 (lp_bid_level_9_volume record) ++
      encode_bytes 11 (ask_level_10_price record) ++
      encode_bytes 11 (bid_level_10_price record) ++
      encode_bytes 12 (ask_level_10_volume record) ++
      encode_bytes 12 (bid_level_10_volume record) ++
      encode_bytes 12 (lp_ask_level_10_volume record) ++
      encode_bytes 12 (lp_bid_level_10_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (board_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (current_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (opening_price_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (todays_high_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (todays_low_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (accumulated_trading_volume_value, bytes) =>
                                          match decode_bytes 22 bytes with
                                          | None => None
                                          | Some (accumulated_trading_value_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trading_halt_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (ask_level_1_price_value, bytes) =>
                                                      match decode_bytes 11 bytes with
                                                      | None => None
                                                      | Some (bid_level_1_price_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (ask_level_1_volume_value, bytes) =>
                                                              match decode_bytes 12 bytes with
                                                              | None => None
                                                              | Some (bid_level_1_volume_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (lp_ask_level_1_volume_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (lp_bid_level_1_volume_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_2_volume_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_2_volume_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (lp_ask_level_2_volume_value, bytes) =>
                                                                                              match decode_bytes 12 bytes with
                                                                                              | None => None
                                                                                              | Some (lp_bid_level_2_volume_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_3_price_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_3_price_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_3_volume_value, bytes) =>
                                                                                                              match decode_bytes 12 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (lp_ask_level_3_volume_value, bytes) =>
                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (lp_bid_level_3_volume_value, bytes) =>
                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (lp_ask_level_4_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (lp_bid_level_4_volume_value, bytes) =>
                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (lp_ask_level_5_volume_value, bytes) =>
                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (lp_bid_level_5_volume_value, bytes) =>
                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_level_6_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (bid_level_6_price_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (lp_ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (lp_bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (ask_level_7_price_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (bid_level_7_price_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (lp_ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (lp_bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (ask_level_8_price_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (lp_ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (lp_bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (ask_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (lp_ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (lp_bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (ask_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (lp_ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (lp_bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (total_ask_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (total_bid_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      Some ({| board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; current_price := current_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; trading_halt := trading_halt_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; lp_ask_level_1_volume := lp_ask_level_1_volume_value; lp_bid_level_1_volume := lp_bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; lp_ask_level_2_volume := lp_ask_level_2_volume_value; lp_bid_level_2_volume := lp_bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; lp_ask_level_3_volume := lp_ask_level_3_volume_value; lp_bid_level_3_volume := lp_bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; lp_ask_level_4_volume := lp_ask_level_4_volume_value; lp_bid_level_4_volume := lp_bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; lp_ask_level_5_volume := lp_ask_level_5_volume_value; lp_bid_level_5_volume := lp_bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; lp_ask_level_6_volume := lp_ask_level_6_volume_value; lp_bid_level_6_volume := lp_bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; lp_ask_level_7_volume := lp_ask_level_7_volume_value; lp_bid_level_7_volume := lp_bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; lp_ask_level_8_volume := lp_ask_level_8_volume_value; lp_bid_level_8_volume := lp_bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; lp_ask_level_9_volume := lp_ask_level_9_volume_value; lp_bid_level_9_volume := lp_bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; lp_ask_level_10_volume := lp_ask_level_10_volume_value; lp_bid_level_10_volume := lp_bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 847.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 bound_75]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_45.
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
      rewrite decode_encode_uint by exact bound_75.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldSnapshotMessage.

  Module SpotGoldNegotiatedTradeMessage.

    (** Spot Gold Negotiated Trade Data. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      negotiated_trade_accumulated_trading_volume : list byte;
      negotiated_trade_accumulated_trading_value : list byte;
      total_accumulated_trading_volume : list byte;
      total_accumulated_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (negotiated_trade_accumulated_trading_volume record) = 15 /\
      Datatypes.length (negotiated_trade_accumulated_trading_value record) = 22 /\
      Datatypes.length (total_accumulated_trading_volume record) = 15 /\
      Datatypes.length (total_accumulated_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 15 (negotiated_trade_accumulated_trading_volume record) ++
      encode_bytes 22 (negotiated_trade_accumulated_trading_value record) ++
      encode_bytes 15 (total_accumulated_trading_volume record) ++
      encode_bytes 22 (total_accumulated_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 15 bytes with
              | None => None
              | Some (negotiated_trade_accumulated_trading_volume_value, bytes) =>
                  match decode_bytes 22 bytes with
                  | None => None
                  | Some (negotiated_trade_accumulated_trading_value_value, bytes) =>
                      match decode_bytes 15 bytes with
                      | None => None
                      | Some (total_accumulated_trading_volume_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (total_accumulated_trading_value_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; negotiated_trade_accumulated_trading_volume := negotiated_trade_accumulated_trading_volume_value; negotiated_trade_accumulated_trading_value := negotiated_trade_accumulated_trading_value_value; total_accumulated_trading_volume := total_accumulated_trading_volume_value; total_accumulated_trading_value := total_accumulated_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldNegotiatedTradeMessage.

  Module EmissionsQuoteMessage.

    (** Emissions Quote. Multi-level bid/ask quotes for Emissions. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_volume record) = 12 /\
      Datatypes.length (bid_level_1_volume record) = 12 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_volume record) = 12 /\
      Datatypes.length (bid_level_2_volume record) = 12 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_volume record) = 12 /\
      Datatypes.length (bid_level_3_volume record) = 12 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_volume record) = 12 /\
      Datatypes.length (bid_level_4_volume record) = 12 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_volume record) = 12 /\
      Datatypes.length (bid_level_5_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 12 (ask_level_1_volume record) ++
      encode_bytes 12 (bid_level_1_volume record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 12 (ask_level_2_volume record) ++
      encode_bytes 12 (bid_level_2_volume record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 12 (ask_level_3_volume record) ++
      encode_bytes 12 (bid_level_3_volume record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 12 (ask_level_4_volume record) ++
      encode_bytes 12 (bid_level_4_volume record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 12 (ask_level_5_volume record) ++
      encode_bytes 12 (bid_level_5_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (ask_level_1_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (bid_level_1_price_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (ask_level_1_volume_value, bytes) =>
                                          match decode_bytes 12 bytes with
                                          | None => None
                                          | Some (bid_level_1_volume_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (ask_level_2_price_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (bid_level_2_price_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (ask_level_2_volume_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (bid_level_2_volume_value, bytes) =>
                                                              match decode_bytes 11 bytes with
                                                              | None => None
                                                              | Some (ask_level_3_price_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (bid_level_3_price_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_3_volume_value, bytes) =>
                                                                          match decode_bytes 12 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_3_volume_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_4_price_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_4_price_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_level_4_volume_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_level_4_volume_value, bytes) =>
                                                                                              match decode_bytes 11 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_level_5_price_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_level_5_price_value, bytes) =>
                                                                                                      match decode_bytes 12 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_5_volume_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_5_volume_value, bytes) =>
                                                                                                              match decode_bytes 12 bytes with
                                                                                                              | None => None
                                                                                                              | Some (total_ask_volume_value, bytes) =>
                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (total_bid_volume_value, bytes) =>
                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (estimated_trading_price_value, bytes) =>
                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 320.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 bound_30]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_30.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsQuoteMessage.

  Module EmissionsOrderFilledMessage.

    (** Emissions Order Filled. Real-time trade prints with running totals. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      previous_price : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (previous_price record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 11 (previous_price record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (trading_volume_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (opening_price_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (todays_high_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (todays_low_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (previous_price_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (accumulated_trading_volume_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_value_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (final_ask_bid_type_code_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; previous_price := previous_price_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 141.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsOrderFilledMessage.

  Module EmissionsOrderFilledPlusQuoteMessage.

    (** Emissions Order Filled plus Quote. Trade print followed by full quote state. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      previous_price : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (previous_price record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_volume record) = 12 /\
      Datatypes.length (bid_level_1_volume record) = 12 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_volume record) = 12 /\
      Datatypes.length (bid_level_2_volume record) = 12 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_volume record) = 12 /\
      Datatypes.length (bid_level_3_volume record) = 12 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_volume record) = 12 /\
      Datatypes.length (bid_level_4_volume record) = 12 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_volume record) = 12 /\
      Datatypes.length (bid_level_5_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 11 (previous_price record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 12 (ask_level_1_volume record) ++
      encode_bytes 12 (bid_level_1_volume record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 12 (ask_level_2_volume record) ++
      encode_bytes 12 (bid_level_2_volume record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 12 (ask_level_3_volume record) ++
      encode_bytes 12 (bid_level_3_volume record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 12 (ask_level_4_volume record) ++
      encode_bytes 12 (bid_level_4_volume record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 12 (ask_level_5_volume record) ++
      encode_bytes 12 (bid_level_5_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (trading_volume_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (opening_price_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (todays_high_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (todays_low_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (previous_price_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (accumulated_trading_volume_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_value_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (final_ask_bid_type_code_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (ask_level_1_price_value, bytes) =>
                                                                      match decode_bytes 11 bytes with
                                                                      | None => None
                                                                      | Some (bid_level_1_price_value, bytes) =>
                                                                          match decode_bytes 12 bytes with
                                                                          | None => None
                                                                          | Some (ask_level_1_volume_value, bytes) =>
                                                                              match decode_bytes 12 bytes with
                                                                              | None => None
                                                                              | Some (bid_level_1_volume_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_2_price_value, bytes) =>
                                                                                      match decode_bytes 11 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_2_price_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_2_volume_value, bytes) =>
                                                                                              match decode_bytes 12 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_2_volume_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_3_price_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_3_price_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_3_volume_value, bytes) =>
                                                                                                              match decode_bytes 12 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_4_price_value, bytes) =>
                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_4_price_value, bytes) =>
                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (total_ask_volume_value, bytes) =>
                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (total_bid_volume_value, bytes) =>
                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; previous_price := previous_price_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 395.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 bound_37]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_37.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsOrderFilledPlusQuoteMessage.

  Module EmissionsMarketOperationTsPlusQuoteMessage.

    (** Emissions Market Operation TS plus Quote. Session-state event followed by full quote state. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : list byte;
      trading_halt_reason_code : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      Datatypes.length (board_event_group_code record) = 5 /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_volume record) = 12 /\
      Datatypes.length (bid_level_1_volume record) = 12 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_volume record) = 12 /\
      Datatypes.length (bid_level_2_volume record) = 12 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_volume record) = 12 /\
      Datatypes.length (bid_level_3_volume record) = 12 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_volume record) = 12 /\
      Datatypes.length (bid_level_4_volume record) = 12 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_volume record) = 12 /\
      Datatypes.length (bid_level_5_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_bytes 5 (board_event_group_code record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 12 (ask_level_1_volume record) ++
      encode_bytes 12 (bid_level_1_volume record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 12 (ask_level_2_volume record) ++
      encode_bytes 12 (bid_level_2_volume record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 12 (ask_level_3_volume record) ++
      encode_bytes 12 (bid_level_3_volume record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 12 (ask_level_4_volume record) ++
      encode_bytes 12 (bid_level_4_volume record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 12 (ask_level_5_volume record) ++
      encode_bytes 12 (bid_level_5_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (board_event_id_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (start_time_of_a_board_event_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (board_event_group_code_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (trading_halt_reason_code_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (ask_level_1_price_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (bid_level_1_price_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (ask_level_1_volume_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (bid_level_1_volume_value, bytes) =>
                                                              match decode_bytes 11 bytes with
                                                              | None => None
                                                              | Some (ask_level_2_price_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (bid_level_2_price_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_2_volume_value, bytes) =>
                                                                          match decode_bytes 12 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_2_volume_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_3_price_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_3_price_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_level_3_volume_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_level_3_volume_value, bytes) =>
                                                                                              match decode_bytes 11 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_level_4_price_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_level_4_price_value, bytes) =>
                                                                                                      match decode_bytes 12 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_4_volume_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_4_volume_value, bytes) =>
                                                                                                              match decode_bytes 11 bytes with
                                                                                                              | None => None
                                                                                                              | Some (ask_level_5_price_value, bytes) =>
                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (bid_level_5_price_value, bytes) =>
                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (total_ask_volume_value, bytes) =>
                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (total_bid_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; trading_halt_reason_code := trading_halt_reason_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 340.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 bound_34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_34.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsMarketOperationTsPlusQuoteMessage.

  Module EmissionsSnapshotMessage.

    (** Emissions Market Data Snapshot. Periodic full state snapshot. *)
    Record t := {
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      current_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      negotiated_block_trade_trading_volume : list byte;
      negotiated_block_trade_trading_value : list byte;
      trading_halt : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (current_price record) = 11 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (negotiated_block_trade_trading_volume record) = 12 /\
      Datatypes.length (negotiated_block_trade_trading_value record) = 22 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_volume record) = 12 /\
      Datatypes.length (bid_level_1_volume record) = 12 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_volume record) = 12 /\
      Datatypes.length (bid_level_2_volume record) = 12 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_volume record) = 12 /\
      Datatypes.length (bid_level_3_volume record) = 12 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_volume record) = 12 /\
      Datatypes.length (bid_level_4_volume record) = 12 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_volume record) = 12 /\
      Datatypes.length (bid_level_5_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 11 (current_price record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 12 (negotiated_block_trade_trading_volume record) ++
      encode_bytes 22 (negotiated_block_trade_trading_value record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 12 (ask_level_1_volume record) ++
      encode_bytes 12 (bid_level_1_volume record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 12 (ask_level_2_volume record) ++
      encode_bytes 12 (bid_level_2_volume record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 12 (ask_level_3_volume record) ++
      encode_bytes 12 (bid_level_3_volume record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 12 (ask_level_4_volume record) ++
      encode_bytes 12 (bid_level_4_volume record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 12 (ask_level_5_volume record) ++
      encode_bytes 12 (bid_level_5_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (board_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (session_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (current_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (opening_price_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (todays_high_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (todays_low_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (accumulated_trading_volume_value, bytes) =>
                                          match decode_bytes 22 bytes with
                                          | None => None
                                          | Some (accumulated_trading_value_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (negotiated_block_trade_trading_volume_value, bytes) =>
                                                  match decode_bytes 22 bytes with
                                                  | None => None
                                                  | Some (negotiated_block_trade_trading_value_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trading_halt_value, bytes) =>
                                                          match decode_bytes 11 bytes with
                                                          | None => None
                                                          | Some (ask_level_1_price_value, bytes) =>
                                                              match decode_bytes 11 bytes with
                                                              | None => None
                                                              | Some (bid_level_1_price_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (ask_level_1_volume_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (bid_level_1_volume_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_2_volume_value, bytes) =>
                                                                                      match decode_bytes 12 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_2_volume_value, bytes) =>
                                                                                          match decode_bytes 11 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_3_price_value, bytes) =>
                                                                                              match decode_bytes 11 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_3_price_value, bytes) =>
                                                                                                  match decode_bytes 12 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_3_volume_value, bytes) =>
                                                                                                      match decode_bytes 12 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_3_volume_value, bytes) =>
                                                                                                          match decode_bytes 11 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                              match decode_bytes 11 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_5_price_value, bytes) =>
                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (total_ask_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (total_bid_volume_value, bytes) =>
                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                              Some ({| board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; current_price := current_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; negotiated_block_trade_trading_volume := negotiated_block_trade_trading_volume_value; negotiated_block_trade_trading_value := negotiated_block_trade_trading_value_value; trading_halt := trading_halt_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 411.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 bound_37]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_37.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsSnapshotMessage.

  Module EmissionsNegotiatedTradeMessage.

    (** Emissions Negotiated Trade Data. *)
    Record t := {
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (board_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (a_designated_number_for_an_issue_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (trading_price_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (trading_volume_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (accumulated_trading_volume_value, bytes) =>
                              match decode_bytes 22 bytes with
                              | None => None
                              | Some (accumulated_trading_value_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; trading_price := trading_price_value; trading_volume := trading_volume_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsNegotiatedTradeMessage.

  Module EmissionsDeterminationOfBasePriceMessage.

    (** Emissions Determination of Base Price. Per-issue base price assignment. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      base_price : list byte;
      upper_limit_of_base_price : list byte;
      lower_limit_of_base_price : list byte;
      block_trading_upper_limit_price : list byte;
      block_trading_lower_limit_price : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (base_price record) = 11 /\
      Datatypes.length (upper_limit_of_base_price record) = 11 /\
      Datatypes.length (lower_limit_of_base_price record) = 11 /\
      Datatypes.length (block_trading_upper_limit_price record) = 11 /\
      Datatypes.length (block_trading_lower_limit_price record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 11 (base_price record) ++
      encode_bytes 11 (upper_limit_of_base_price record) ++
      encode_bytes 11 (lower_limit_of_base_price record) ++
      encode_bytes 11 (block_trading_upper_limit_price record) ++
      encode_bytes 11 (block_trading_lower_limit_price record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (base_price_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (upper_limit_of_base_price_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (lower_limit_of_base_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (block_trading_upper_limit_price_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (block_trading_lower_limit_price_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; base_price := base_price_value; upper_limit_of_base_price := upper_limit_of_base_price_value; lower_limit_of_base_price := lower_limit_of_base_price_value; block_trading_upper_limit_price := block_trading_upper_limit_price_value; block_trading_lower_limit_price := block_trading_lower_limit_price_value; end_keyword := end_keyword_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 84.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsDeterminationOfBasePriceMessage.

  Module EmissionsAuctionResultsMessage.

    (** Emissions Auction Results per Issue. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      auction_bid_volume : list byte;
      auction_price : list byte;
      auction_volume : list byte;
      volume_in_the_bid_invitation : list byte;
      number_of_bidders : list byte;
      bid_to_cover_ratio : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (auction_bid_volume record) = 12 /\
      Datatypes.length (auction_price record) = 11 /\
      Datatypes.length (auction_volume record) = 12 /\
      Datatypes.length (volume_in_the_bid_invitation record) = 12 /\
      Datatypes.length (number_of_bidders record) = 13 /\
      Datatypes.length (bid_to_cover_ratio record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (auction_bid_volume record) ++
      encode_bytes 11 (auction_price record) ++
      encode_bytes 12 (auction_volume record) ++
      encode_bytes 12 (volume_in_the_bid_invitation record) ++
      encode_bytes 13 (number_of_bidders record) ++
      encode_bytes 11 (bid_to_cover_ratio record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (auction_bid_volume_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (auction_price_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (auction_volume_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (volume_in_the_bid_invitation_value, bytes) =>
                              match decode_bytes 13 bytes with
                              | None => None
                              | Some (number_of_bidders_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (bid_to_cover_ratio_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (end_keyword_value, bytes) =>
                                          Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; auction_bid_volume := auction_bid_volume_value; auction_price := auction_price_value; auction_volume := auction_volume_value; volume_in_the_bid_invitation := volume_in_the_bid_invitation_value; number_of_bidders := number_of_bidders_value; bid_to_cover_ratio := bid_to_cover_ratio_value; end_keyword := end_keyword_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 90.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsAuctionResultsMessage.

  Module SpotGoldBatchDataMessage.

    (** Spot Gold Batch Data. Per-issue reference data dumped at start-of-day. *)
    Record t := {
      message_sequence_number : list byte;
      total_number_of_instruments_of_the_contract : list byte;
      business_date : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      abbreviated_issue_code : list byte;
      issue_name : list byte;
      abbreviated_issue_name : list byte;
      english_issue_name : list byte;
      abbreviated_issue_name_in_en : list byte;
      market_operation_product_id : list byte;
      security_group_id : list byte;
      listing_date : list byte;
      delisting_date : list byte;
      market_id : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      base_price : list byte;
      random_end_trigger_code : list byte;
      trading_halt : list byte;
      unit_of_volume_in_main_board : list byte;
      yesterdays_closing_price : list byte;
      yesterdays_closing_price_type_code : list byte;
      substitute_price_of_securities : list byte;
      appraisal_ratio_of_substitute_price : list byte;
      a_representative_issue_to_calculate_base_price : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (total_number_of_instruments_of_the_contract record) = 6 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (abbreviated_issue_code record) = 9 /\
      Datatypes.length (issue_name record) = 80 /\
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (english_issue_name record) = 80 /\
      Datatypes.length (abbreviated_issue_name_in_en record) = 40 /\
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (security_group_id record) = 2 /\
      Datatypes.length (listing_date record) = 8 /\
      Datatypes.length (delisting_date record) = 8 /\
      Datatypes.length (market_id record) = 3 /\
      Datatypes.length (upper_limit_price record) = 11 /\
      Datatypes.length (lower_limit_price record) = 11 /\
      Datatypes.length (base_price record) = 11 /\
      Datatypes.length (random_end_trigger_code record) = 1 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (unit_of_volume_in_main_board record) = 11 /\
      Datatypes.length (yesterdays_closing_price record) = 11 /\
      Datatypes.length (yesterdays_closing_price_type_code record) = 1 /\
      Datatypes.length (substitute_price_of_securities record) = 11 /\
      Datatypes.length (appraisal_ratio_of_substitute_price record) = 13 /\
      Datatypes.length (a_representative_issue_to_calculate_base_price record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 6 (total_number_of_instruments_of_the_contract record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 9 (abbreviated_issue_code record) ++
      encode_bytes 80 (issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 80 (english_issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name_in_en record) ++
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 2 (security_group_id record) ++
      encode_bytes 8 (listing_date record) ++
      encode_bytes 8 (delisting_date record) ++
      encode_bytes 3 (market_id record) ++
      encode_bytes 11 (upper_limit_price record) ++
      encode_bytes 11 (lower_limit_price record) ++
      encode_bytes 11 (base_price record) ++
      encode_bytes 1 (random_end_trigger_code record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 11 (unit_of_volume_in_main_board record) ++
      encode_bytes 11 (yesterdays_closing_price record) ++
      encode_bytes 1 (yesterdays_closing_price_type_code record) ++
      encode_bytes 11 (substitute_price_of_securities record) ++
      encode_bytes 13 (appraisal_ratio_of_substitute_price record) ++
      encode_bytes 12 (a_representative_issue_to_calculate_base_price record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (total_number_of_instruments_of_the_contract_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (business_date_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (abbreviated_issue_code_value, bytes) =>
                              match decode_bytes 80 bytes with
                              | None => None
                              | Some (issue_name_value, bytes) =>
                                  match decode_bytes 40 bytes with
                                  | None => None
                                  | Some (abbreviated_issue_name_value, bytes) =>
                                      match decode_bytes 80 bytes with
                                      | None => None
                                      | Some (english_issue_name_value, bytes) =>
                                          match decode_bytes 40 bytes with
                                          | None => None
                                          | Some (abbreviated_issue_name_in_en_value, bytes) =>
                                              match decode_bytes 3 bytes with
                                              | None => None
                                              | Some (market_operation_product_id_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (security_group_id_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (listing_date_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (delisting_date_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (market_id_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (upper_limit_price_value, bytes) =>
                                                                      match decode_bytes 11 bytes with
                                                                      | None => None
                                                                      | Some (lower_limit_price_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (base_price_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (random_end_trigger_code_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trading_halt_value, bytes) =>
                                                                                      match decode_bytes 11 bytes with
                                                                                      | None => None
                                                                                      | Some (unit_of_volume_in_main_board_value, bytes) =>
                                                                                          match decode_bytes 11 bytes with
                                                                                          | None => None
                                                                                          | Some (yesterdays_closing_price_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (yesterdays_closing_price_type_code_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (substitute_price_of_securities_value, bytes) =>
                                                                                                      match decode_bytes 13 bytes with
                                                                                                      | None => None
                                                                                                      | Some (appraisal_ratio_of_substitute_price_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (a_representative_issue_to_calculate_base_price_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; total_number_of_instruments_of_the_contract := total_number_of_instruments_of_the_contract_value; business_date := business_date_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; abbreviated_issue_code := abbreviated_issue_code_value; issue_name := issue_name_value; abbreviated_issue_name := abbreviated_issue_name_value; english_issue_name := english_issue_name_value; abbreviated_issue_name_in_en := abbreviated_issue_name_in_en_value; market_operation_product_id := market_operation_product_id_value; security_group_id := security_group_id_value; listing_date := listing_date_value; delisting_date := delisting_date_value; market_id := market_id_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; base_price := base_price_value; random_end_trigger_code := random_end_trigger_code_value; trading_halt := trading_halt_value; unit_of_volume_in_main_board := unit_of_volume_in_main_board_value; yesterdays_closing_price := yesterdays_closing_price_value; yesterdays_closing_price_type_code := yesterdays_closing_price_type_code_value; substitute_price_of_securities := substitute_price_of_securities_value; appraisal_ratio_of_substitute_price := appraisal_ratio_of_substitute_price_value; a_representative_issue_to_calculate_base_price := a_representative_issue_to_calculate_base_price_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 408.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldBatchDataMessage.

  Module EmissionsBatchDataMessage.

    (** Emissions Batch Data. Per-issue reference data dumped at start-of-day. *)
    Record t := {
      message_sequence_number : list byte;
      total_number_of_instruments_of_the_contract : list byte;
      business_date : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      abbreviated_issue_code : list byte;
      issue_name : list byte;
      abbreviated_issue_name : list byte;
      english_issue_name : list byte;
      abbreviated_issue_name_in_en : list byte;
      market_operation_product_id : list byte;
      security_group_id : list byte;
      listing_date : list byte;
      delisting_date : list byte;
      market_id : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      base_price : list byte;
      random_end_trigger_code : list byte;
      trading_halt : list byte;
      unit_of_volume_in_main_board : list byte;
      yesterdays_closing_price : list byte;
      yesterdays_closing_price_type_code : list byte;
      substitute_price_of_securities : list byte;
      appraisal_ratio_of_substitute_price : list byte;
      a_representative_issue_to_calculate_base_price : list byte;
      an_issue_of_which_base_price_is_settled_with_a_todays_single_price : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (total_number_of_instruments_of_the_contract record) = 6 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (abbreviated_issue_code record) = 9 /\
      Datatypes.length (issue_name record) = 80 /\
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (english_issue_name record) = 80 /\
      Datatypes.length (abbreviated_issue_name_in_en record) = 40 /\
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (security_group_id record) = 2 /\
      Datatypes.length (listing_date record) = 8 /\
      Datatypes.length (delisting_date record) = 8 /\
      Datatypes.length (market_id record) = 3 /\
      Datatypes.length (upper_limit_price record) = 11 /\
      Datatypes.length (lower_limit_price record) = 11 /\
      Datatypes.length (base_price record) = 11 /\
      Datatypes.length (random_end_trigger_code record) = 1 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (unit_of_volume_in_main_board record) = 11 /\
      Datatypes.length (yesterdays_closing_price record) = 11 /\
      Datatypes.length (yesterdays_closing_price_type_code record) = 1 /\
      Datatypes.length (substitute_price_of_securities record) = 11 /\
      Datatypes.length (appraisal_ratio_of_substitute_price record) = 13 /\
      Datatypes.length (a_representative_issue_to_calculate_base_price record) = 12 /\
      Datatypes.length (an_issue_of_which_base_price_is_settled_with_a_todays_single_price record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 6 (total_number_of_instruments_of_the_contract record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 9 (abbreviated_issue_code record) ++
      encode_bytes 80 (issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 80 (english_issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name_in_en record) ++
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 2 (security_group_id record) ++
      encode_bytes 8 (listing_date record) ++
      encode_bytes 8 (delisting_date record) ++
      encode_bytes 3 (market_id record) ++
      encode_bytes 11 (upper_limit_price record) ++
      encode_bytes 11 (lower_limit_price record) ++
      encode_bytes 11 (base_price record) ++
      encode_bytes 1 (random_end_trigger_code record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 11 (unit_of_volume_in_main_board record) ++
      encode_bytes 11 (yesterdays_closing_price record) ++
      encode_bytes 1 (yesterdays_closing_price_type_code record) ++
      encode_bytes 11 (substitute_price_of_securities record) ++
      encode_bytes 13 (appraisal_ratio_of_substitute_price record) ++
      encode_bytes 12 (a_representative_issue_to_calculate_base_price record) ++
      encode_bytes 1 (an_issue_of_which_base_price_is_settled_with_a_todays_single_price record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (total_number_of_instruments_of_the_contract_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (business_date_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (abbreviated_issue_code_value, bytes) =>
                              match decode_bytes 80 bytes with
                              | None => None
                              | Some (issue_name_value, bytes) =>
                                  match decode_bytes 40 bytes with
                                  | None => None
                                  | Some (abbreviated_issue_name_value, bytes) =>
                                      match decode_bytes 80 bytes with
                                      | None => None
                                      | Some (english_issue_name_value, bytes) =>
                                          match decode_bytes 40 bytes with
                                          | None => None
                                          | Some (abbreviated_issue_name_in_en_value, bytes) =>
                                              match decode_bytes 3 bytes with
                                              | None => None
                                              | Some (market_operation_product_id_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (security_group_id_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (listing_date_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (delisting_date_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (market_id_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (upper_limit_price_value, bytes) =>
                                                                      match decode_bytes 11 bytes with
                                                                      | None => None
                                                                      | Some (lower_limit_price_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (base_price_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (random_end_trigger_code_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (trading_halt_value, bytes) =>
                                                                                      match decode_bytes 11 bytes with
                                                                                      | None => None
                                                                                      | Some (unit_of_volume_in_main_board_value, bytes) =>
                                                                                          match decode_bytes 11 bytes with
                                                                                          | None => None
                                                                                          | Some (yesterdays_closing_price_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (yesterdays_closing_price_type_code_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (substitute_price_of_securities_value, bytes) =>
                                                                                                      match decode_bytes 13 bytes with
                                                                                                      | None => None
                                                                                                      | Some (appraisal_ratio_of_substitute_price_value, bytes) =>
                                                                                                          match decode_bytes 12 bytes with
                                                                                                          | None => None
                                                                                                          | Some (a_representative_issue_to_calculate_base_price_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (an_issue_of_which_base_price_is_settled_with_a_todays_single_price_value, bytes) =>
                                                                                                                  match decode_uint 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; total_number_of_instruments_of_the_contract := total_number_of_instruments_of_the_contract_value; business_date := business_date_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; abbreviated_issue_code := abbreviated_issue_code_value; issue_name := issue_name_value; abbreviated_issue_name := abbreviated_issue_name_value; english_issue_name := english_issue_name_value; abbreviated_issue_name_in_en := abbreviated_issue_name_in_en_value; market_operation_product_id := market_operation_product_id_value; security_group_id := security_group_id_value; listing_date := listing_date_value; delisting_date := delisting_date_value; market_id := market_id_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; base_price := base_price_value; random_end_trigger_code := random_end_trigger_code_value; trading_halt := trading_halt_value; unit_of_volume_in_main_board := unit_of_volume_in_main_board_value; yesterdays_closing_price := yesterdays_closing_price_value; yesterdays_closing_price_type_code := yesterdays_closing_price_type_code_value; substitute_price_of_securities := substitute_price_of_securities_value; appraisal_ratio_of_substitute_price := appraisal_ratio_of_substitute_price_value; a_representative_issue_to_calculate_base_price := a_representative_issue_to_calculate_base_price_value; an_issue_of_which_base_price_is_settled_with_a_todays_single_price := an_issue_of_which_base_price_is_settled_with_a_todays_single_price_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 409.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 bound_27]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_27.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsBatchDataMessage.

  Module ExternalGoldSpotClosingPriceMessage.

    (** External Gold Spot (Closing Price) (IFMSRID0036) — Commodities A CMD variant. NESTED-BRANCH NOTE: TR-CODE M200G is shared with the Real-time variant (IFMSRID0035); the Data Type field (field 3) discriminates between Closing Price and Real-time. The loader will need an inner Branch on Data Type once the nested-Branch shape is settled. Real-time variant deferred. *)
    Record t := {
      data_type : list byte;
      job_code_symbol : list byte;
      trading_date : list byte;
      trading_time : list byte;
      opening_price : list byte;
      high_price : list byte;
      low_price : list byte;
      closing_price : list byte;
      change_from_previous_day_sign : list byte;
      change_from_previous_day : list byte;
      fluctuating_rate : list byte;
      bid_quote : list byte;
      ask_quote : list byte;
      currency_code : list byte;
      conversion_basic_exchange_rate : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (data_type record) = 1 /\
      Datatypes.length (job_code_symbol record) = 16 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (trading_time record) = 6 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (high_price record) = 9 /\
      Datatypes.length (low_price record) = 9 /\
      Datatypes.length (closing_price record) = 11 /\
      Datatypes.length (change_from_previous_day_sign record) = 1 /\
      Datatypes.length (change_from_previous_day record) = 9 /\
      Datatypes.length (fluctuating_rate record) = 9 /\
      Datatypes.length (bid_quote record) = 9 /\
      Datatypes.length (ask_quote record) = 9 /\
      Datatypes.length (currency_code record) = 6 /\
      Datatypes.length (conversion_basic_exchange_rate record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (data_type record) ++
      encode_bytes 16 (job_code_symbol record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 6 (trading_time record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 9 (high_price record) ++
      encode_bytes 9 (low_price record) ++
      encode_bytes 11 (closing_price record) ++
      encode_bytes 1 (change_from_previous_day_sign record) ++
      encode_bytes 9 (change_from_previous_day record) ++
      encode_bytes 9 (fluctuating_rate record) ++
      encode_bytes 9 (bid_quote record) ++
      encode_bytes 9 (ask_quote record) ++
      encode_bytes 6 (currency_code record) ++
      encode_bytes 9 (conversion_basic_exchange_rate record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (data_type_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (job_code_symbol_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trading_date_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (trading_time_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (opening_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (high_price_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (low_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (closing_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (change_from_previous_day_sign_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (change_from_previous_day_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (fluctuating_rate_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (bid_quote_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (ask_quote_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (currency_code_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (conversion_basic_exchange_rate_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| data_type := data_type_value; job_code_symbol := job_code_symbol_value; trading_date := trading_date_value; trading_time := trading_time_value; opening_price := opening_price_value; high_price := high_price_value; low_price := low_price_value; closing_price := closing_price_value; change_from_previous_day_sign := change_from_previous_day_sign_value; change_from_previous_day := change_from_previous_day_value; fluctuating_rate := fluctuating_rate_value; bid_quote := bid_quote_value; ask_quote := ask_quote_value; currency_code := currency_code_value; conversion_basic_exchange_rate := conversion_basic_exchange_rate_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 122.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalGoldSpotClosingPriceMessage.

  Module SpotGoldMarketOperationTsMessage.

    (** Spot Gold Market Operation TS. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : list byte;
      trading_halt_reason_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      Datatypes.length (board_event_group_code record) = 5 /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_bytes 5 (board_event_group_code record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (board_event_id_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (start_time_of_a_board_event_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (board_event_group_code_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (trading_halt_reason_code_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (end_keyword_value, bytes) =>
                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; trading_halt_reason_code := trading_halt_reason_code_value; end_keyword := end_keyword_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldMarketOperationTsMessage.

  Module SpotGoldIssueClosingMessage.

    (** Spot Gold Issue Closing. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      closing_price : list byte;
      closing_price_type_code : list byte;
      filler_11 : list byte;
      second_filler_11 : list byte;
      closing_price_weighted_stock_price_average : list byte;
      closing_price_base_price_of_buy_in : list byte;
      closing_price_upper_limit_of_buy_in : list byte;
      closing_price_lower_limit_of_buy_in : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (closing_price record) = 11 /\
      Datatypes.length (closing_price_type_code record) = 1 /\
      Datatypes.length (filler_11 record) = 11 /\
      Datatypes.length (second_filler_11 record) = 11 /\
      Datatypes.length (closing_price_weighted_stock_price_average record) = 11 /\
      Datatypes.length (closing_price_base_price_of_buy_in record) = 11 /\
      Datatypes.length (closing_price_upper_limit_of_buy_in record) = 11 /\
      Datatypes.length (closing_price_lower_limit_of_buy_in record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 11 (closing_price record) ++
      encode_bytes 1 (closing_price_type_code record) ++
      encode_bytes 11 (filler_11 record) ++
      encode_bytes 11 (second_filler_11 record) ++
      encode_bytes 11 (closing_price_weighted_stock_price_average record) ++
      encode_bytes 11 (closing_price_base_price_of_buy_in record) ++
      encode_bytes 11 (closing_price_upper_limit_of_buy_in record) ++
      encode_bytes 11 (closing_price_lower_limit_of_buy_in record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (closing_price_type_code_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (filler_11_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (second_filler_11_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (closing_price_weighted_stock_price_average_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (closing_price_base_price_of_buy_in_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (closing_price_upper_limit_of_buy_in_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (closing_price_lower_limit_of_buy_in_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (end_keyword_value, bytes) =>
                                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; closing_price := closing_price_value; closing_price_type_code := closing_price_type_code_value; filler_11 := filler_11_value; second_filler_11 := second_filler_11_value; closing_price_weighted_stock_price_average := closing_price_weighted_stock_price_average_value; closing_price_base_price_of_buy_in := closing_price_base_price_of_buy_in_value; closing_price_upper_limit_of_buy_in := closing_price_upper_limit_of_buy_in_value; closing_price_lower_limit_of_buy_in := closing_price_lower_limit_of_buy_in_value; end_keyword := end_keyword_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 107.
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
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldIssueClosingMessage.

  Module SpotGoldMarketOperationScheduleMessage.

    (** Spot Gold Market Operation Schedule. *)
    Record t := {
      market_operation_product_id : list byte;
      board_id : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : list byte;
      session_start_end_code : list byte;
      session_id : list byte;
      isin_code : list byte;
      isin_code_of_a_common_stock : list byte;
      product_id : list byte;
      trading_halt_reason_code : list byte;
      trading_halt_type_code : list byte;
      step_applied : list byte;
      price_limit_range_expansion_for_base_issue_type_code : list byte;
      expected_time_of_expanding_price_limit_range : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      Datatypes.length (board_event_group_code record) = 5 /\
      Datatypes.length (session_start_end_code record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (isin_code_of_a_common_stock record) = 12 /\
      Datatypes.length (product_id record) = 11 /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      Datatypes.length (trading_halt_type_code record) = 1 /\
      Datatypes.length (step_applied record) = 2 /\
      Datatypes.length (price_limit_range_expansion_for_base_issue_type_code record) = 1 /\
      Datatypes.length (expected_time_of_expanding_price_limit_range record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_bytes 5 (board_event_group_code record) ++
      encode_bytes 2 (session_start_end_code record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (isin_code_of_a_common_stock record) ++
      encode_bytes 11 (product_id record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_bytes 1 (trading_halt_type_code record) ++
      encode_bytes 2 (step_applied record) ++
      encode_bytes 1 (price_limit_range_expansion_for_base_issue_type_code record) ++
      encode_bytes 9 (expected_time_of_expanding_price_limit_range record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (market_operation_product_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (board_event_id_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (start_time_of_a_board_event_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (board_event_group_code_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (session_start_end_code_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (session_id_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (isin_code_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (isin_code_of_a_common_stock_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (product_id_value, bytes) =>
                                              match decode_bytes 3 bytes with
                                              | None => None
                                              | Some (trading_halt_reason_code_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trading_halt_type_code_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (step_applied_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (price_limit_range_expansion_for_base_issue_type_code_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (expected_time_of_expanding_price_limit_range_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| market_operation_product_id := market_operation_product_id_value; board_id := board_id_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; session_start_end_code := session_start_end_code_value; session_id := session_id_value; isin_code := isin_code_value; isin_code_of_a_common_stock := isin_code_of_a_common_stock_value; product_id := product_id_value; trading_halt_reason_code := trading_halt_reason_code_value; trading_halt_type_code := trading_halt_type_code_value; step_applied := step_applied_value; price_limit_range_expansion_for_base_issue_type_code := price_limit_range_expansion_for_base_issue_type_code_value; expected_time_of_expanding_price_limit_range := expected_time_of_expanding_price_limit_range_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 78.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldMarketOperationScheduleMessage.

  Module EmissionsMarketOperationTsMessage.

    (** Emissions Market Operation TS. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : list byte;
      trading_halt_reason_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      Datatypes.length (board_event_group_code record) = 5 /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_bytes 5 (board_event_group_code record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (board_event_id_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (start_time_of_a_board_event_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (board_event_group_code_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (trading_halt_reason_code_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (end_keyword_value, bytes) =>
                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; trading_halt_reason_code := trading_halt_reason_code_value; end_keyword := end_keyword_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsMarketOperationTsMessage.

  Module EmissionsIssueClosingMessage.

    (** Emissions Issue Closing. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      closing_price : list byte;
      closing_price_type_code : list byte;
      filler_11 : list byte;
      second_filler_11 : list byte;
      closing_price_weighted_stock_price_average : list byte;
      closing_price_base_price_of_buy_in : list byte;
      closing_price_upper_limit_of_buy_in : list byte;
      closing_price_lower_limit_of_buy_in : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (closing_price record) = 11 /\
      Datatypes.length (closing_price_type_code record) = 1 /\
      Datatypes.length (filler_11 record) = 11 /\
      Datatypes.length (second_filler_11 record) = 11 /\
      Datatypes.length (closing_price_weighted_stock_price_average record) = 11 /\
      Datatypes.length (closing_price_base_price_of_buy_in record) = 11 /\
      Datatypes.length (closing_price_upper_limit_of_buy_in record) = 11 /\
      Datatypes.length (closing_price_lower_limit_of_buy_in record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 11 (closing_price record) ++
      encode_bytes 1 (closing_price_type_code record) ++
      encode_bytes 11 (filler_11 record) ++
      encode_bytes 11 (second_filler_11 record) ++
      encode_bytes 11 (closing_price_weighted_stock_price_average record) ++
      encode_bytes 11 (closing_price_base_price_of_buy_in record) ++
      encode_bytes 11 (closing_price_upper_limit_of_buy_in record) ++
      encode_bytes 11 (closing_price_lower_limit_of_buy_in record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (closing_price_type_code_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (filler_11_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (second_filler_11_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (closing_price_weighted_stock_price_average_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (closing_price_base_price_of_buy_in_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (closing_price_upper_limit_of_buy_in_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (closing_price_lower_limit_of_buy_in_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (end_keyword_value, bytes) =>
                                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; closing_price := closing_price_value; closing_price_type_code := closing_price_type_code_value; filler_11 := filler_11_value; second_filler_11 := second_filler_11_value; closing_price_weighted_stock_price_average := closing_price_weighted_stock_price_average_value; closing_price_base_price_of_buy_in := closing_price_base_price_of_buy_in_value; closing_price_upper_limit_of_buy_in := closing_price_upper_limit_of_buy_in_value; closing_price_lower_limit_of_buy_in := closing_price_lower_limit_of_buy_in_value; end_keyword := end_keyword_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 107.
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
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsIssueClosingMessage.

  Module EmissionsMarketOperationScheduleMessage.

    (** Emissions Market Operation Schedule. *)
    Record t := {
      market_operation_product_id : list byte;
      board_id : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : list byte;
      session_start_end_code : list byte;
      session_id : list byte;
      isin_code : list byte;
      isin_code_of_a_common_stock : list byte;
      product_id : list byte;
      trading_halt_reason_code : list byte;
      trading_halt_type_code : list byte;
      step_applied : list byte;
      price_limit_range_expansion_for_base_issue_type_code : list byte;
      expected_time_of_expanding_price_limit_range : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      Datatypes.length (board_event_group_code record) = 5 /\
      Datatypes.length (session_start_end_code record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (isin_code_of_a_common_stock record) = 12 /\
      Datatypes.length (product_id record) = 11 /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      Datatypes.length (trading_halt_type_code record) = 1 /\
      Datatypes.length (step_applied record) = 2 /\
      Datatypes.length (price_limit_range_expansion_for_base_issue_type_code record) = 1 /\
      Datatypes.length (expected_time_of_expanding_price_limit_range record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_bytes 5 (board_event_group_code record) ++
      encode_bytes 2 (session_start_end_code record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (isin_code_of_a_common_stock record) ++
      encode_bytes 11 (product_id record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_bytes 1 (trading_halt_type_code record) ++
      encode_bytes 2 (step_applied record) ++
      encode_bytes 1 (price_limit_range_expansion_for_base_issue_type_code record) ++
      encode_bytes 9 (expected_time_of_expanding_price_limit_range record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (market_operation_product_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (board_event_id_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (start_time_of_a_board_event_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (board_event_group_code_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (session_start_end_code_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (session_id_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (isin_code_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (isin_code_of_a_common_stock_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (product_id_value, bytes) =>
                                              match decode_bytes 3 bytes with
                                              | None => None
                                              | Some (trading_halt_reason_code_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (trading_halt_type_code_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (step_applied_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (price_limit_range_expansion_for_base_issue_type_code_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (expected_time_of_expanding_price_limit_range_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| market_operation_product_id := market_operation_product_id_value; board_id := board_id_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; session_start_end_code := session_start_end_code_value; session_id := session_id_value; isin_code := isin_code_value; isin_code_of_a_common_stock := isin_code_of_a_common_stock_value; product_id := product_id_value; trading_halt_reason_code := trading_halt_reason_code_value; trading_halt_type_code := trading_halt_type_code_value; step_applied := step_applied_value; price_limit_range_expansion_for_base_issue_type_code := price_limit_range_expansion_for_base_issue_type_code_value; expected_time_of_expanding_price_limit_range := expected_time_of_expanding_price_limit_range_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 78.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EmissionsMarketOperationScheduleMessage.

  Module SpotGoldRandomEndMessage.

    (** Spot Gold Random End. Reports random extension of the call auction window when conditional random-end is triggered. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      random_end_trigger_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (random_end_trigger_code record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 1 (random_end_trigger_code record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (random_end_trigger_code_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; random_end_trigger_code := random_end_trigger_code_value; end_keyword := end_keyword_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotGoldRandomEndMessage.

End KoscomMdcsRealtimeCommoditiesV2020.
