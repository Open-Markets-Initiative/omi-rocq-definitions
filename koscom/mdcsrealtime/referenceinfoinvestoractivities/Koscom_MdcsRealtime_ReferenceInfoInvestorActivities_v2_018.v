From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Koscom Co., Ltd. MDCS Realtime Reference Info and Investor Activities

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

Module KoscomMdcsRealtimeReferenceInfoInvestorActivitiesV2018.

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
      Datatypes.length (accumulated_trading_value record) = 12 /\
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
      encode_bytes 12 (accumulated_trading_value record) ++
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
                                  match decode_bytes 12 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
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
      Datatypes.length (accumulated_trading_value record) = 12 /\
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
      encode_bytes 12 (accumulated_trading_value record) ++
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
                                  match decode_bytes 12 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
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
      Datatypes.length (currency_code record) = 3 /\
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
      encode_bytes 3 (currency_code record) ++
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
                                  match decode_bytes 3 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 59.
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

  Module SecuritiesInvestorActivitiesPerIndustryMessage.

    (** Investor Activities per Industry. Aggregated bid/ask volumes and values per investor category and industry. *)
    Record t := {
      calculation_time : list byte;
      investor_code : list byte;
      index_id : list byte;
      isin_code : list byte;
      accumulated_ask_trading_volume : list byte;
      accumulated_ask_trading_value : list byte;
      accumulated_bid_trading_volume : list byte;
      accumulated_bid_trading_value : list byte;
      filler_3 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (calculation_time record) = 6 /\
      Datatypes.length (investor_code record) = 4 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (accumulated_ask_trading_volume record) = 12 /\
      Datatypes.length (accumulated_ask_trading_value record) = 22 /\
      Datatypes.length (accumulated_bid_trading_volume record) = 12 /\
      Datatypes.length (accumulated_bid_trading_value record) = 22 /\
      Datatypes.length (filler_3 record) = 3 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (calculation_time record) ++
      encode_bytes 4 (investor_code record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (accumulated_ask_trading_volume record) ++
      encode_bytes 22 (accumulated_ask_trading_value record) ++
      encode_bytes 12 (accumulated_bid_trading_volume record) ++
      encode_bytes 22 (accumulated_bid_trading_value record) ++
      encode_bytes 3 (filler_3 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (calculation_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (investor_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (index_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (isin_code_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (accumulated_ask_trading_volume_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (accumulated_ask_trading_value_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (accumulated_bid_trading_volume_value, bytes) =>
                                  match decode_bytes 22 bytes with
                                  | None => None
                                  | Some (accumulated_bid_trading_value_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (filler_3_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| calculation_time := calculation_time_value; investor_code := investor_code_value; index_id := index_id_value; isin_code := isin_code_value; accumulated_ask_trading_volume := accumulated_ask_trading_volume_value; accumulated_ask_trading_value := accumulated_ask_trading_value_value; accumulated_bid_trading_volume := accumulated_bid_trading_volume_value; accumulated_bid_trading_value := accumulated_bid_trading_value_value; filler_3 := filler_3_value; end_keyword := end_keyword_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 100.
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

  End SecuritiesInvestorActivitiesPerIndustryMessage.

  Module SecuritiesInvestorActivitiesPerIssueEodMessage.

    (** Investor Activities per Issue EOD. Aggregated bid/ask volumes and values per investor category and ISIN at end-of-day. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      investor_code : list byte;
      accumulated_ask_trading_volume : list byte;
      accumulated_ask_trading_value : list byte;
      accumulated_bid_trading_volume : list byte;
      accumulated_bid_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (investor_code record) = 4 /\
      Datatypes.length (accumulated_ask_trading_volume record) = 12 /\
      Datatypes.length (accumulated_ask_trading_value record) = 22 /\
      Datatypes.length (accumulated_bid_trading_volume record) = 12 /\
      Datatypes.length (accumulated_bid_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 4 (investor_code record) ++
      encode_bytes 12 (accumulated_ask_trading_volume record) ++
      encode_bytes 22 (accumulated_ask_trading_value record) ++
      encode_bytes 12 (accumulated_bid_trading_volume record) ++
      encode_bytes 22 (accumulated_bid_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (investor_code_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (accumulated_ask_trading_volume_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (accumulated_ask_trading_value_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (accumulated_bid_trading_volume_value, bytes) =>
                              match decode_bytes 22 bytes with
                              | None => None
                              | Some (accumulated_bid_trading_value_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; investor_code := investor_code_value; accumulated_ask_trading_volume := accumulated_ask_trading_volume_value; accumulated_ask_trading_value := accumulated_ask_trading_value_value; accumulated_bid_trading_volume := accumulated_bid_trading_volume_value; accumulated_bid_trading_value := accumulated_bid_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 91.
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

  End SecuritiesInvestorActivitiesPerIssueEodMessage.

  Module SecuritiesInvestorActivitiesPerCommoditiesMessage.

    (** Investor Activities per Commodities. *)
    Record t := {
      calculation_time : list byte;
      investor_code : list byte;
      accumulated_ask_trading_volume : list byte;
      accumulated_ask_trading_value : list byte;
      accumulated_bid_trading_volume : list byte;
      accumulated_bid_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (calculation_time record) = 6 /\
      Datatypes.length (investor_code record) = 4 /\
      Datatypes.length (accumulated_ask_trading_volume record) = 12 /\
      Datatypes.length (accumulated_ask_trading_value record) = 22 /\
      Datatypes.length (accumulated_bid_trading_volume record) = 12 /\
      Datatypes.length (accumulated_bid_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (calculation_time record) ++
      encode_bytes 4 (investor_code record) ++
      encode_bytes 12 (accumulated_ask_trading_volume record) ++
      encode_bytes 22 (accumulated_ask_trading_value record) ++
      encode_bytes 12 (accumulated_bid_trading_volume record) ++
      encode_bytes 22 (accumulated_bid_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (calculation_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (investor_code_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (accumulated_ask_trading_volume_value, bytes) =>
                  match decode_bytes 22 bytes with
                  | None => None
                  | Some (accumulated_ask_trading_value_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (accumulated_bid_trading_volume_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (accumulated_bid_trading_value_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| calculation_time := calculation_time_value; investor_code := investor_code_value; accumulated_ask_trading_volume := accumulated_ask_trading_volume_value; accumulated_ask_trading_value := accumulated_ask_trading_value_value; accumulated_bid_trading_volume := accumulated_bid_trading_volume_value; accumulated_bid_trading_value := accumulated_bid_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 79.
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

  End SecuritiesInvestorActivitiesPerCommoditiesMessage.

  Module SecuritiesShortSellingMessage.

    (** Short Selling activity per issue. *)
    Record t := {
      isin_code : list byte;
      covered_short_selling_trading_volume : list byte;
      covered_short_selling_trading_value : list byte;
      uptick_rule_applied_covered_short_selling_trading_volume : list byte;
      uptick_rule_applied_covered_short_selling_trading_value : list byte;
      uptick_rule_unapplied_covered_short_selling_trading_volume : list byte;
      uptick_rule_unapplied_covered_short_selling_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (covered_short_selling_trading_volume record) = 12 /\
      Datatypes.length (covered_short_selling_trading_value record) = 22 /\
      Datatypes.length (uptick_rule_applied_covered_short_selling_trading_volume record) = 12 /\
      Datatypes.length (uptick_rule_applied_covered_short_selling_trading_value record) = 22 /\
      Datatypes.length (uptick_rule_unapplied_covered_short_selling_trading_volume record) = 12 /\
      Datatypes.length (uptick_rule_unapplied_covered_short_selling_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (covered_short_selling_trading_volume record) ++
      encode_bytes 22 (covered_short_selling_trading_value record) ++
      encode_bytes 12 (uptick_rule_applied_covered_short_selling_trading_volume record) ++
      encode_bytes 22 (uptick_rule_applied_covered_short_selling_trading_value record) ++
      encode_bytes 12 (uptick_rule_unapplied_covered_short_selling_trading_volume record) ++
      encode_bytes 22 (uptick_rule_unapplied_covered_short_selling_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (covered_short_selling_trading_volume_value, bytes) =>
              match decode_bytes 22 bytes with
              | None => None
              | Some (covered_short_selling_trading_value_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (uptick_rule_applied_covered_short_selling_trading_volume_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (uptick_rule_applied_covered_short_selling_trading_value_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (uptick_rule_unapplied_covered_short_selling_trading_volume_value, bytes) =>
                              match decode_bytes 22 bytes with
                              | None => None
                              | Some (uptick_rule_unapplied_covered_short_selling_trading_value_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| isin_code := isin_code_value; covered_short_selling_trading_volume := covered_short_selling_trading_volume_value; covered_short_selling_trading_value := covered_short_selling_trading_value_value; uptick_rule_applied_covered_short_selling_trading_volume := uptick_rule_applied_covered_short_selling_trading_volume_value; uptick_rule_applied_covered_short_selling_trading_value := uptick_rule_applied_covered_short_selling_trading_value_value; uptick_rule_unapplied_covered_short_selling_trading_volume := uptick_rule_unapplied_covered_short_selling_trading_volume_value; uptick_rule_unapplied_covered_short_selling_trading_value := uptick_rule_unapplied_covered_short_selling_trading_value_value; end_keyword := end_keyword_value |}, bytes)
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

  End SecuritiesShortSellingMessage.

  Module SecuritiesTreasuryStocksTradedMessage.

    (** Treasury Stocks Traded Information. Real-time treasury-stock trade dissemination per issue. *)
    Record t := {
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      bid_treasury_stock_declaration_id : list byte;
      ask_treasury_stock_declaration_id : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (bid_treasury_stock_declaration_id record) = 5 /\
      Datatypes.length (ask_treasury_stock_declaration_id record) = 5 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 5 (bid_treasury_stock_declaration_id record) ++
      encode_bytes 5 (ask_treasury_stock_declaration_id record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                  | Some (trading_price_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (trading_volume_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (bid_treasury_stock_declaration_id_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (ask_treasury_stock_declaration_id_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; trading_price := trading_price_value; trading_volume := trading_volume_value; bid_treasury_stock_declaration_id := bid_treasury_stock_declaration_id_value; ask_treasury_stock_declaration_id := ask_treasury_stock_declaration_id_value; end_keyword := end_keyword_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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

  End SecuritiesTreasuryStocksTradedMessage.

  Module SecuritiesBuyInVolumeMessage.

    (** Buy-in Volume reference. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      transmission_date : list byte;
      buy_in_type_code : list byte;
      security_group_id : list byte;
      buy_in_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (transmission_date record) = 8 /\
      Datatypes.length (buy_in_type_code record) = 1 /\
      Datatypes.length (security_group_id record) = 2 /\
      Datatypes.length (buy_in_volume record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (transmission_date record) ++
      encode_bytes 1 (buy_in_type_code record) ++
      encode_bytes 2 (security_group_id record) ++
      encode_bytes 15 (buy_in_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (transmission_date_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (buy_in_type_code_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (security_group_id_value, bytes) =>
                          match decode_bytes 15 bytes with
                          | None => None
                          | Some (buy_in_volume_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; transmission_date := transmission_date_value; buy_in_type_code := buy_in_type_code_value; security_group_id := security_group_id_value; buy_in_volume := buy_in_volume_value; end_keyword := end_keyword_value |}, bytes)
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

  End SecuritiesBuyInVolumeMessage.

End KoscomMdcsRealtimeReferenceInfoInvestorActivitiesV2018.
