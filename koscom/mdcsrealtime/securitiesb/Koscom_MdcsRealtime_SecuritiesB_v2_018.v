From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Koscom Co., Ltd. MDCS Realtime Securities B

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

Module KoscomMdcsRealtimeSecuritiesBV2018.

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

  Module SecuritiesQuoteMmLpExcludedMessage.

    (** Securities Quote (MM/LP Quotes Excluded). Multi-level bid/ask quotes and remaining quantities for KOSPI/KOSDAQ/KONEX equities. *)
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
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      midpoint : list byte;
      ask_mid_price_total_volume : list byte;
      bid_mid_price_total_volume : list byte;
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
      Datatypes.length (ask_level_6_price record) = 11 /\
      Datatypes.length (bid_level_6_price record) = 11 /\
      Datatypes.length (ask_level_6_volume record) = 12 /\
      Datatypes.length (bid_level_6_volume record) = 12 /\
      Datatypes.length (ask_level_7_price record) = 11 /\
      Datatypes.length (bid_level_7_price record) = 11 /\
      Datatypes.length (ask_level_7_volume record) = 12 /\
      Datatypes.length (bid_level_7_volume record) = 12 /\
      Datatypes.length (ask_level_8_price record) = 11 /\
      Datatypes.length (bid_level_8_price record) = 11 /\
      Datatypes.length (ask_level_8_volume record) = 12 /\
      Datatypes.length (bid_level_8_volume record) = 12 /\
      Datatypes.length (ask_level_9_price record) = 11 /\
      Datatypes.length (bid_level_9_price record) = 11 /\
      Datatypes.length (ask_level_9_volume record) = 12 /\
      Datatypes.length (bid_level_9_volume record) = 12 /\
      Datatypes.length (ask_level_10_price record) = 11 /\
      Datatypes.length (bid_level_10_price record) = 11 /\
      Datatypes.length (ask_level_10_volume record) = 12 /\
      Datatypes.length (bid_level_10_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      Datatypes.length (midpoint record) = 11 /\
      Datatypes.length (ask_mid_price_total_volume record) = 12 /\
      Datatypes.length (bid_mid_price_total_volume record) = 12 /\
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
      encode_bytes 11 (ask_level_6_price record) ++
      encode_bytes 11 (bid_level_6_price record) ++
      encode_bytes 12 (ask_level_6_volume record) ++
      encode_bytes 12 (bid_level_6_volume record) ++
      encode_bytes 11 (ask_level_7_price record) ++
      encode_bytes 11 (bid_level_7_price record) ++
      encode_bytes 12 (ask_level_7_volume record) ++
      encode_bytes 12 (bid_level_7_volume record) ++
      encode_bytes 11 (ask_level_8_price record) ++
      encode_bytes 11 (bid_level_8_price record) ++
      encode_bytes 12 (ask_level_8_volume record) ++
      encode_bytes 12 (bid_level_8_volume record) ++
      encode_bytes 11 (ask_level_9_price record) ++
      encode_bytes 11 (bid_level_9_price record) ++
      encode_bytes 12 (ask_level_9_volume record) ++
      encode_bytes 12 (bid_level_9_volume record) ++
      encode_bytes 11 (ask_level_10_price record) ++
      encode_bytes 11 (bid_level_10_price record) ++
      encode_bytes 12 (ask_level_10_volume record) ++
      encode_bytes 12 (bid_level_10_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_bytes 11 (midpoint record) ++
      encode_bytes 12 (ask_mid_price_total_volume record) ++
      encode_bytes 12 (bid_mid_price_total_volume record) ++
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
                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (midpoint_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (ask_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bid_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; midpoint := midpoint_value; ask_mid_price_total_volume := ask_mid_price_total_volume_value; bid_mid_price_total_volume := bid_mid_price_total_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 585.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 bound_53]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_53.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesQuoteMmLpExcludedMessage.

  Module SecuritiesQuoteMmLpIncludedMessage.

    (** Securities Quote (MM/LP Quotes Included). Multi-level bid/ask quotes including market maker and liquidity provider quotes. *)
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
      midpoint : list byte;
      ask_mid_price_total_volume : list byte;
      bid_mid_price_total_volume : list byte;
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
      Datatypes.length (midpoint record) = 11 /\
      Datatypes.length (ask_mid_price_total_volume record) = 12 /\
      Datatypes.length (bid_mid_price_total_volume record) = 12 /\
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
      encode_bytes 11 (midpoint record) ++
      encode_bytes 12 (ask_mid_price_total_volume record) ++
      encode_bytes 12 (bid_mid_price_total_volume record) ++
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
                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (midpoint_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (ask_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (bid_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; lp_ask_level_1_volume := lp_ask_level_1_volume_value; lp_bid_level_1_volume := lp_bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; lp_ask_level_2_volume := lp_ask_level_2_volume_value; lp_bid_level_2_volume := lp_bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; lp_ask_level_3_volume := lp_ask_level_3_volume_value; lp_bid_level_3_volume := lp_bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; lp_ask_level_4_volume := lp_ask_level_4_volume_value; lp_bid_level_4_volume := lp_bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; lp_ask_level_5_volume := lp_ask_level_5_volume_value; lp_bid_level_5_volume := lp_bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; lp_ask_level_6_volume := lp_ask_level_6_volume_value; lp_bid_level_6_volume := lp_bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; lp_ask_level_7_volume := lp_ask_level_7_volume_value; lp_bid_level_7_volume := lp_bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; lp_ask_level_8_volume := lp_ask_level_8_volume_value; lp_bid_level_8_volume := lp_bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; lp_ask_level_9_volume := lp_ask_level_9_volume_value; lp_bid_level_9_volume := lp_bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; lp_ask_level_10_volume := lp_ask_level_10_volume_value; lp_bid_level_10_volume := lp_bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; midpoint := midpoint_value; ask_mid_price_total_volume := ask_mid_price_total_volume_value; bid_mid_price_total_volume := bid_mid_price_total_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 825.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 bound_73]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_73.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesQuoteMmLpIncludedMessage.

  Module SecuritiesSnapshotMmLpExcludedMessage.

    (** Equities Snapshot (MM/LP Quotes Excluded). Periodic full state snapshot for KOSPI/KOSDAQ/KONEX equities. *)
    Record t := {
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      price_change_against_previous_day : list byte;
      a_price_change_against_the_previous_day : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      current_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
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
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      closing_price_type_code : list byte;
      trading_halt : list byte;
      midpoint : list byte;
      ask_mid_price_total_volume : list byte;
      bid_mid_price_total_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (price_change_against_previous_day record) = 1 /\
      Datatypes.length (a_price_change_against_the_previous_day record) = 11 /\
      Datatypes.length (upper_limit_price record) = 11 /\
      Datatypes.length (lower_limit_price record) = 11 /\
      Datatypes.length (current_price record) = 11 /\
      Datatypes.length (opening_price record) = 11 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
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
      Datatypes.length (ask_level_6_price record) = 11 /\
      Datatypes.length (bid_level_6_price record) = 11 /\
      Datatypes.length (ask_level_6_volume record) = 12 /\
      Datatypes.length (bid_level_6_volume record) = 12 /\
      Datatypes.length (ask_level_7_price record) = 11 /\
      Datatypes.length (bid_level_7_price record) = 11 /\
      Datatypes.length (ask_level_7_volume record) = 12 /\
      Datatypes.length (bid_level_7_volume record) = 12 /\
      Datatypes.length (ask_level_8_price record) = 11 /\
      Datatypes.length (bid_level_8_price record) = 11 /\
      Datatypes.length (ask_level_8_volume record) = 12 /\
      Datatypes.length (bid_level_8_volume record) = 12 /\
      Datatypes.length (ask_level_9_price record) = 11 /\
      Datatypes.length (bid_level_9_price record) = 11 /\
      Datatypes.length (ask_level_9_volume record) = 12 /\
      Datatypes.length (bid_level_9_volume record) = 12 /\
      Datatypes.length (ask_level_10_price record) = 11 /\
      Datatypes.length (bid_level_10_price record) = 11 /\
      Datatypes.length (ask_level_10_volume record) = 12 /\
      Datatypes.length (bid_level_10_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      Datatypes.length (closing_price_type_code record) = 1 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (midpoint record) = 11 /\
      Datatypes.length (ask_mid_price_total_volume record) = 12 /\
      Datatypes.length (bid_mid_price_total_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 1 (price_change_against_previous_day record) ++
      encode_bytes 11 (a_price_change_against_the_previous_day record) ++
      encode_bytes 11 (upper_limit_price record) ++
      encode_bytes 11 (lower_limit_price record) ++
      encode_bytes 11 (current_price record) ++
      encode_bytes 11 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
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
      encode_bytes 11 (ask_level_6_price record) ++
      encode_bytes 11 (bid_level_6_price record) ++
      encode_bytes 12 (ask_level_6_volume record) ++
      encode_bytes 12 (bid_level_6_volume record) ++
      encode_bytes 11 (ask_level_7_price record) ++
      encode_bytes 11 (bid_level_7_price record) ++
      encode_bytes 12 (ask_level_7_volume record) ++
      encode_bytes 12 (bid_level_7_volume record) ++
      encode_bytes 11 (ask_level_8_price record) ++
      encode_bytes 11 (bid_level_8_price record) ++
      encode_bytes 12 (ask_level_8_volume record) ++
      encode_bytes 12 (bid_level_8_volume record) ++
      encode_bytes 11 (ask_level_9_price record) ++
      encode_bytes 11 (bid_level_9_price record) ++
      encode_bytes 12 (ask_level_9_volume record) ++
      encode_bytes 12 (bid_level_9_volume record) ++
      encode_bytes 11 (ask_level_10_price record) ++
      encode_bytes 11 (bid_level_10_price record) ++
      encode_bytes 12 (ask_level_10_volume record) ++
      encode_bytes 12 (bid_level_10_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_bytes 1 (closing_price_type_code record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 11 (midpoint record) ++
      encode_bytes 12 (ask_mid_price_total_volume record) ++
      encode_bytes 12 (bid_mid_price_total_volume record) ++
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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (price_change_against_previous_day_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (a_price_change_against_the_previous_day_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (upper_limit_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (lower_limit_price_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (current_price_value, bytes) =>
                                          match decode_bytes 11 bytes with
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
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (closing_price_type_code_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (trading_halt_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (midpoint_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (ask_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (bid_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                          Some ({| board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; price_change_against_previous_day := price_change_against_previous_day_value; a_price_change_against_the_previous_day := a_price_change_against_the_previous_day_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; current_price := current_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; closing_price_type_code := closing_price_type_code_value; trading_halt := trading_halt_value; midpoint := midpoint_value; ask_mid_price_total_volume := ask_mid_price_total_volume_value; bid_mid_price_total_volume := bid_mid_price_total_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 680.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 bound_64]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_64.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesSnapshotMmLpExcludedMessage.

  Module SecuritiesSnapshotMmLpIncludedMessage.

    (** Equities Snapshot (MM/LP Quotes Included). Periodic full state snapshot including MM/LP quotes for Securities C. *)
    Record t := {
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      price_change_against_previous_day : list byte;
      a_price_change_against_the_previous_day : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      current_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
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
      closing_price_type_code : list byte;
      trading_halt : list byte;
      knock_out_elw_type_code : list byte;
      knock_out_elw_triggering_time : list byte;
      midpoint : list byte;
      ask_mid_price_total_volume : list byte;
      bid_mid_price_total_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (price_change_against_previous_day record) = 1 /\
      Datatypes.length (a_price_change_against_the_previous_day record) = 11 /\
      Datatypes.length (upper_limit_price record) = 11 /\
      Datatypes.length (lower_limit_price record) = 11 /\
      Datatypes.length (current_price record) = 11 /\
      Datatypes.length (opening_price record) = 11 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
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
      Datatypes.length (closing_price_type_code record) = 1 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (knock_out_elw_type_code record) = 1 /\
      Datatypes.length (knock_out_elw_triggering_time record) = 9 /\
      Datatypes.length (midpoint record) = 11 /\
      Datatypes.length (ask_mid_price_total_volume record) = 12 /\
      Datatypes.length (bid_mid_price_total_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 1 (price_change_against_previous_day record) ++
      encode_bytes 11 (a_price_change_against_the_previous_day record) ++
      encode_bytes 11 (upper_limit_price record) ++
      encode_bytes 11 (lower_limit_price record) ++
      encode_bytes 11 (current_price record) ++
      encode_bytes 11 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
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
      encode_bytes 1 (closing_price_type_code record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 1 (knock_out_elw_type_code record) ++
      encode_bytes 9 (knock_out_elw_triggering_time record) ++
      encode_bytes 11 (midpoint record) ++
      encode_bytes 12 (ask_mid_price_total_volume record) ++
      encode_bytes 12 (bid_mid_price_total_volume record) ++
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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (price_change_against_previous_day_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (a_price_change_against_the_previous_day_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (upper_limit_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (lower_limit_price_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (current_price_value, bytes) =>
                                          match decode_bytes 11 bytes with
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
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (closing_price_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (trading_halt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (knock_out_elw_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (knock_out_elw_triggering_time_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (midpoint_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (ask_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (bid_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  Some ({| board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; price_change_against_previous_day := price_change_against_previous_day_value; a_price_change_against_the_previous_day := a_price_change_against_the_previous_day_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; current_price := current_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; lp_ask_level_1_volume := lp_ask_level_1_volume_value; lp_bid_level_1_volume := lp_bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; lp_ask_level_2_volume := lp_ask_level_2_volume_value; lp_bid_level_2_volume := lp_bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; lp_ask_level_3_volume := lp_ask_level_3_volume_value; lp_bid_level_3_volume := lp_bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; lp_ask_level_4_volume := lp_ask_level_4_volume_value; lp_bid_level_4_volume := lp_bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; lp_ask_level_5_volume := lp_ask_level_5_volume_value; lp_bid_level_5_volume := lp_bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; lp_ask_level_6_volume := lp_ask_level_6_volume_value; lp_bid_level_6_volume := lp_bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; lp_ask_level_7_volume := lp_ask_level_7_volume_value; lp_bid_level_7_volume := lp_bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; lp_ask_level_8_volume := lp_ask_level_8_volume_value; lp_bid_level_8_volume := lp_bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; lp_ask_level_9_volume := lp_ask_level_9_volume_value; lp_bid_level_9_volume := lp_bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; lp_ask_level_10_volume := lp_ask_level_10_volume_value; lp_bid_level_10_volume := lp_bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; closing_price_type_code := closing_price_type_code_value; trading_halt := trading_halt_value; knock_out_elw_type_code := knock_out_elw_type_code_value; knock_out_elw_triggering_time := knock_out_elw_triggering_time_value; midpoint := midpoint_value; ask_mid_price_total_volume := ask_mid_price_total_volume_value; bid_mid_price_total_volume := bid_mid_price_total_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 930.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 bound_86]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_bytes by exact bound_80.
      rewrite decode_encode_bytes by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_bytes by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_bytes by exact bound_85.
      rewrite decode_encode_uint by exact bound_86.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesSnapshotMmLpIncludedMessage.

  Module SecuritiesOrderFilledMessage.

    (** Securities Order Filled. Real-time trade prints with running totals for KOSPI/KOSDAQ/KONEX equities. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      price_change_against_previous_day : list byte;
      a_price_change_against_the_previous_day : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      lp_holding_quantity : list byte;
      the_best_ask : list byte;
      the_best_bid : list byte;
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
      Datatypes.length (price_change_against_previous_day record) = 1 /\
      Datatypes.length (a_price_change_against_the_previous_day record) = 11 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (opening_price record) = 11 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (lp_holding_quantity record) = 15 /\
      Datatypes.length (the_best_ask record) = 11 /\
      Datatypes.length (the_best_bid record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 1 (price_change_against_previous_day record) ++
      encode_bytes 11 (a_price_change_against_the_previous_day record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 11 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 15 (lp_holding_quantity record) ++
      encode_bytes 11 (the_best_ask record) ++
      encode_bytes 11 (the_best_bid record) ++
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
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (price_change_against_previous_day_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (a_price_change_against_the_previous_day_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (trading_price_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (trading_volume_value, bytes) =>
                                              match decode_bytes 11 bytes with
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
                                                                  | Some (final_ask_bid_type_code_value, bytes) =>
                                                                      match decode_bytes 15 bytes with
                                                                      | None => None
                                                                      | Some (lp_holding_quantity_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (the_best_ask_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (the_best_bid_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; price_change_against_previous_day := price_change_against_previous_day_value; a_price_change_against_the_previous_day := a_price_change_against_the_previous_day_value; trading_price := trading_price_value; trading_volume := trading_volume_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; lp_holding_quantity := lp_holding_quantity_value; the_best_ask := the_best_ask_value; the_best_bid := the_best_bid_value; end_keyword := end_keyword_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 181.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesOrderFilledMessage.

  Module SecuritiesNegotiatedTradeMessage.

    (** Securities Negotiated Trade Data. Off-book negotiated trades for KOSPI/KOSDAQ/KONEX equities. *)
    Record t := {
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
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
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (accumulated_trading_volume_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (accumulated_trading_value_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
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

  End SecuritiesNegotiatedTradeMessage.

  Module SecuritiesMarketOperationTsMessage.

    (** Securities Market Operation TS. Per-issue session-state events (halts, resumes, expirations) for KOSPI/KOSDAQ/KONEX. *)
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

  End SecuritiesMarketOperationTsMessage.

  Module SecuritiesDeterminationOfBasePriceMessage.

    (** Determination of Base Price. Per-issue base price assignment events. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      base_price : list byte;
      upper_limit_of_base_price : list byte;
      lower_limit_of_base_price : list byte;
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
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 11 (base_price record) ++
      encode_bytes 11 (upper_limit_of_base_price record) ++
      encode_bytes 11 (lower_limit_of_base_price record) ++
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
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; base_price := base_price_value; upper_limit_of_base_price := upper_limit_of_base_price_value; lower_limit_of_base_price := lower_limit_of_base_price_value; end_keyword := end_keyword_value |}, bytes)
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

  End SecuritiesDeterminationOfBasePriceMessage.

  Module SecuritiesIssueClosingMessage.

    (** Securities Issue Closing. Per-issue closing event for KOSPI/KOSDAQ/KONEX. *)
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

  End SecuritiesIssueClosingMessage.

  Module SecuritiesMarketOperationScheduleMessage.

    (** Securities Market Operation Schedule. Session-level schedule and configuration changes. *)
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

  End SecuritiesMarketOperationScheduleMessage.

  Module SecuritiesRandomEndMessage.

    (** Random End. Reports random extension of the call auction window when conditional random-end is triggered. *)
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

  End SecuritiesRandomEndMessage.

  Module SecuritiesTriggeringViMessage.

    (** Triggering/Removing VI (Volatility Interruption). Per-issue VI trigger or release event. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      the_time_ending_vi : list byte;
      vi_status_code : list byte;
      vi_type_code : list byte;
      a_base_price_to_trigger_static_vi : list byte;
      a_base_price_to_trigger_dynamic_vi : list byte;
      vi_triggering_price : list byte;
      disparate_ratio_to_trigger_static_vi : list byte;
      disparate_ratio_to_trigger_dynamic_vi : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (the_time_ending_vi record) = 9 /\
      Datatypes.length (vi_status_code record) = 1 /\
      Datatypes.length (vi_type_code record) = 1 /\
      Datatypes.length (a_base_price_to_trigger_static_vi record) = 11 /\
      Datatypes.length (a_base_price_to_trigger_dynamic_vi record) = 11 /\
      Datatypes.length (vi_triggering_price record) = 11 /\
      Datatypes.length (disparate_ratio_to_trigger_static_vi record) = 13 /\
      Datatypes.length (disparate_ratio_to_trigger_dynamic_vi record) = 13 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 9 (the_time_ending_vi record) ++
      encode_bytes 1 (vi_status_code record) ++
      encode_bytes 1 (vi_type_code record) ++
      encode_bytes 11 (a_base_price_to_trigger_static_vi record) ++
      encode_bytes 11 (a_base_price_to_trigger_dynamic_vi record) ++
      encode_bytes 11 (vi_triggering_price record) ++
      encode_bytes 13 (disparate_ratio_to_trigger_static_vi record) ++
      encode_bytes 13 (disparate_ratio_to_trigger_dynamic_vi record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (the_time_ending_vi_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (vi_status_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (vi_type_code_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (a_base_price_to_trigger_static_vi_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (a_base_price_to_trigger_dynamic_vi_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (vi_triggering_price_value, bytes) =>
                                                  match decode_bytes 13 bytes with
                                                  | None => None
                                                  | Some (disparate_ratio_to_trigger_static_vi_value, bytes) =>
                                                      match decode_bytes 13 bytes with
                                                      | None => None
                                                      | Some (disparate_ratio_to_trigger_dynamic_vi_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (end_keyword_value, bytes) =>
                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; the_time_ending_vi := the_time_ending_vi_value; vi_status_code := vi_status_code_value; vi_type_code := vi_type_code_value; a_base_price_to_trigger_static_vi := a_base_price_to_trigger_static_vi_value; a_base_price_to_trigger_dynamic_vi := a_base_price_to_trigger_dynamic_vi_value; vi_triggering_price := vi_triggering_price_value; disparate_ratio_to_trigger_static_vi := disparate_ratio_to_trigger_static_vi_value; disparate_ratio_to_trigger_dynamic_vi := disparate_ratio_to_trigger_dynamic_vi_value; end_keyword := end_keyword_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 111.
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

  End SecuritiesTriggeringViMessage.

  Module SecuritiesQuantityAllocationMessage.

    (** Quantity Allocation. Reports the quantity allocated to each price level at a single price trade match. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      start_end_of_allocation : list byte;
      allocation_type_code : list byte;
      time_when_allocation_ended : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (start_end_of_allocation record) = 1 /\
      Datatypes.length (allocation_type_code record) = 1 /\
      Datatypes.length (time_when_allocation_ended record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 1 (start_end_of_allocation record) ++
      encode_bytes 1 (allocation_type_code record) ++
      encode_bytes 9 (time_when_allocation_ended record) ++
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
                      | Some (start_end_of_allocation_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (allocation_type_code_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (time_when_allocation_ended_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; start_end_of_allocation := start_end_of_allocation_value; allocation_type_code := allocation_type_code_value; time_when_allocation_ended := time_when_allocation_ended_value; end_keyword := end_keyword_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End SecuritiesQuantityAllocationMessage.

  Module SecuritiesMemberFirmSanctionsMessage.

    (** Securities Member Firm Imposing/Lifting of Sanctions. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      disclosing_data_type_code : list byte;
      disclosure_time : list byte;
      member_number : list byte;
      member_firm_trust_principal_type_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (disclosing_data_type_code record) = 3 /\
      Datatypes.length (disclosure_time record) = 9 /\
      Datatypes.length (member_number record) = 5 /\
      Datatypes.length (member_firm_trust_principal_type_code record) = 5 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 3 (disclosing_data_type_code record) ++
      encode_bytes 9 (disclosure_time record) ++
      encode_bytes 5 (member_number record) ++
      encode_bytes 5 (member_firm_trust_principal_type_code record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (disclosing_data_type_code_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (disclosure_time_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (member_number_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (member_firm_trust_principal_type_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; disclosing_data_type_code := disclosing_data_type_code_value; disclosure_time := disclosure_time_value; member_number := member_number_value; member_firm_trust_principal_type_code := member_firm_trust_principal_type_code_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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

  End SecuritiesMemberFirmSanctionsMessage.

  Module SecuritiesEquitiesChangesOfBatchDataMessage.

    (** Equities Changes of Batch data. Mid-day updates to issue-level batch reference fields. *)
    Record t := {
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      disclosing_data_type_code : list byte;
      base_price : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      appraised_price : list byte;
      highest_order_price : list byte;
      lowest_order_price : list byte;
      type_code_for_an_issue_of_which_base_price_is_settled_with_a_todays_single_price : list byte;
      rights_type_code : list byte;
      par_value_type_code : list byte;
      lot_sizes : list byte;
      number_of_listed_shares : list byte;
      designation : list byte;
      closing_price_trading_in_the_pre_opening_market : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (disclosing_data_type_code record) = 3 /\
      Datatypes.length (base_price record) = 11 /\
      Datatypes.length (upper_limit_price record) = 11 /\
      Datatypes.length (lower_limit_price record) = 11 /\
      Datatypes.length (appraised_price record) = 11 /\
      Datatypes.length (highest_order_price record) = 11 /\
      Datatypes.length (lowest_order_price record) = 11 /\
      Datatypes.length (type_code_for_an_issue_of_which_base_price_is_settled_with_a_todays_single_price record) = 1 /\
      Datatypes.length (rights_type_code record) = 2 /\
      Datatypes.length (par_value_type_code record) = 2 /\
      Datatypes.length (lot_sizes record) = 11 /\
      Datatypes.length (number_of_listed_shares record) = 16 /\
      Datatypes.length (designation record) = 1 /\
      Datatypes.length (closing_price_trading_in_the_pre_opening_market record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 3 (disclosing_data_type_code record) ++
      encode_bytes 11 (base_price record) ++
      encode_bytes 11 (upper_limit_price record) ++
      encode_bytes 11 (lower_limit_price record) ++
      encode_bytes 11 (appraised_price record) ++
      encode_bytes 11 (highest_order_price record) ++
      encode_bytes 11 (lowest_order_price record) ++
      encode_bytes 1 (type_code_for_an_issue_of_which_base_price_is_settled_with_a_todays_single_price record) ++
      encode_bytes 2 (rights_type_code record) ++
      encode_bytes 2 (par_value_type_code record) ++
      encode_bytes 11 (lot_sizes record) ++
      encode_bytes 16 (number_of_listed_shares record) ++
      encode_bytes 1 (designation record) ++
      encode_bytes 1 (closing_price_trading_in_the_pre_opening_market record) ++
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
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (disclosing_data_type_code_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (base_price_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (upper_limit_price_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (lower_limit_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (appraised_price_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (highest_order_price_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (lowest_order_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (type_code_for_an_issue_of_which_base_price_is_settled_with_a_todays_single_price_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (rights_type_code_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (par_value_type_code_value, bytes) =>
                                                          match decode_bytes 11 bytes with
                                                          | None => None
                                                          | Some (lot_sizes_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (number_of_listed_shares_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (designation_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (closing_price_trading_in_the_pre_opening_market_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (end_keyword_value, bytes) =>
                                                                              Some ({| board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; disclosing_data_type_code := disclosing_data_type_code_value; base_price := base_price_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; appraised_price := appraised_price_value; highest_order_price := highest_order_price_value; lowest_order_price := lowest_order_price_value; type_code_for_an_issue_of_which_base_price_is_settled_with_a_todays_single_price := type_code_for_an_issue_of_which_base_price_is_settled_with_a_todays_single_price_value; rights_type_code := rights_type_code_value; par_value_type_code := par_value_type_code_value; lot_sizes := lot_sizes_value; number_of_listed_shares := number_of_listed_shares_value; designation := designation_value; closing_price_trading_in_the_pre_opening_market := closing_price_trading_in_the_pre_opening_market_value; end_keyword := end_keyword_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 124.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesEquitiesChangesOfBatchDataMessage.

  Module SecuritiesGroupOrderAcceptanceHaltMessage.

    (** Group Order Acceptance Halt/Release. Matching engine group-order halt and release events. *)
    Record t := {
      market_id : list byte;
      me_group_number : list byte;
      board_id : list byte;
      board_event_id : list byte;
      board_event_group_code : list byte;
      board_event_processing_time : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_id record) = 3 /\
      Datatypes.length (me_group_number record) = 5 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (board_event_group_code record) = 5 /\
      Datatypes.length (board_event_processing_time record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (market_id record) ++
      encode_bytes 5 (me_group_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 5 (board_event_group_code record) ++
      encode_bytes 9 (board_event_processing_time record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (me_group_number_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (board_id_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (board_event_id_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (board_event_group_code_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (board_event_processing_time_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| market_id := market_id_value; me_group_number := me_group_number_value; board_id := board_id_value; board_event_id := board_event_id_value; board_event_group_code := board_event_group_code_value; board_event_processing_time := board_event_processing_time_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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

  End SecuritiesGroupOrderAcceptanceHaltMessage.

  Module SecuritiesEquitiesBatchDataMessage.

    (** Equities Batch Data. Comprehensive per-issue reference data dumped at start-of-day for KOSPI/KOSDAQ/KONEX equities. *)
    Record t := {
      message_sequence_number : list byte;
      total_number_of_instruments_of_the_contract : list byte;
      business_date : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      abbreviated_issue_code : list byte;
      abbreviated_issue_name : list byte;
      abbreviated_issue_name_in_en : list byte;
      group_number : list byte;
      market_operation_product_id : list byte;
      security_group_id : list byte;
      discrete_time_trading : list byte;
      rights_type_code : list byte;
      par_value_type_code : list byte;
      an_issue_of_which_base_price_is_settled_with_a_todays_single_price : list byte;
      reevaluation_reason_code : list byte;
      base_price_change : list byte;
      random_end_trigger_code : list byte;
      market_alert : list byte;
      market_alert_type_code : list byte;
      korea_corporate_governance_stock_price_index_kogi : list byte;
      issue_for_administration : list byte;
      unfaithful_disclosure : list byte;
      back_door_listing : list byte;
      trading_halt : list byte;
      industry_id : list byte;
      small_medium_sized_business : list byte;
      section_type_code : list byte;
      investment_institution_type_code : list byte;
      base_price : list byte;
      yesterdays_closing_price_type_code : list byte;
      yesterdays_closing_price : list byte;
      yesterdays_accumulated_trading_amount : list byte;
      yesterdays_accumulated_trading_value : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      substitute_price_of_securities : list byte;
      par_value : list byte;
      issuing_price : list byte;
      listing_date : list byte;
      number_of_listed_shares : list byte;
      liquidation_trade : list byte;
      the_establishment_date : list byte;
      maturity_date : list byte;
      exercising_period : list byte;
      expiration_date_for_right : list byte;
      exercise_price_of_elw_or_bw : list byte;
      capital : list byte;
      credit_order_possibillity : list byte;
      limit_order_permission_type_code : list byte;
      market_price_order_permission_type_code : list byte;
      conditioned_order_permission_type_code : list byte;
      best_favorable_order_permission_type_code : list byte;
      first_best_order_permission_type_code : list byte;
      mid_price_order_permission_type_code : list byte;
      stop_limit_price_order_permission_type_code : list byte;
      capital_increase_type_code : list byte;
      other_stock_type_code : list byte;
      national_stock : list byte;
      appraised_price : list byte;
      lowest_order_price : list byte;
      highest_order_price : list byte;
      unit_of_volume_in_main_board : list byte;
      lot_size_after_hours_trading : list byte;
      rei_ts_type_code : list byte;
      target_stock_isin_code : list byte;
      currency_iso_code : list byte;
      country_code : list byte;
      market_making_possibility : list byte;
      closing_price_trading_possibility_in_the_after_hours : list byte;
      closing_price_trading_in_the_pre_opening_market : list byte;
      block_trading_in_the_pre_opening_market : list byte;
      basket_trading_in_the_pre_opening_market : list byte;
      announcement_of_estimated_trading_price : list byte;
      short_selling : list byte;
      etf_tracking_difference : list byte;
      regs : list byte;
      spac : list byte;
      tax_type_code : list byte;
      appraisal_ratio_of_substitute_price : list byte;
      investment_caution_issue : list byte;
      delisting_date : list byte;
      short_term_overheat_issue_type_code : list byte;
      etf_replication_methods_type_code : list byte;
      expiration_date : list byte;
      distribution_type_code : list byte;
      calculation_of_redemption_price_start_date : list byte;
      calculation_of_redemption_price_end_date : list byte;
      etp_product_type_code : list byte;
      index_calculation_institution_type_code : list byte;
      index_market_classification_id : list byte;
      index_sequence_number : list byte;
      tracking_index_leverage_inverse_type_code : list byte;
      reference_index_leverage_inverse_type_code : list byte;
      index_asset_classification_id_1 : list byte;
      index_asset_classification_id_2 : list byte;
      ipo_underwriter_member_number : list byte;
      lp_order : list byte;
      low_liquidity : list byte;
      abnormal_rise : list byte;
      upper_limit_quantity : list byte;
      investment_precaution_issue : list byte;
      preferred_stocks_with_lesser_shares : list byte;
      spac_merger : list byte;
      segment_type_code : list byte;
      after_market_possibility : list byte;
      pre_market_possibility : list byte;
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
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (abbreviated_issue_name_in_en record) = 40 /\
      Datatypes.length (group_number record) = 5 /\
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (security_group_id record) = 2 /\
      Datatypes.length (discrete_time_trading record) = 1 /\
      Datatypes.length (rights_type_code record) = 2 /\
      Datatypes.length (par_value_type_code record) = 2 /\
      Datatypes.length (an_issue_of_which_base_price_is_settled_with_a_todays_single_price record) = 1 /\
      Datatypes.length (reevaluation_reason_code record) = 2 /\
      Datatypes.length (base_price_change record) = 1 /\
      Datatypes.length (random_end_trigger_code record) = 1 /\
      Datatypes.length (market_alert record) = 1 /\
      Datatypes.length (market_alert_type_code record) = 2 /\
      Datatypes.length (korea_corporate_governance_stock_price_index_kogi record) = 1 /\
      Datatypes.length (issue_for_administration record) = 1 /\
      Datatypes.length (unfaithful_disclosure record) = 1 /\
      Datatypes.length (back_door_listing record) = 1 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (industry_id record) = 10 /\
      Datatypes.length (small_medium_sized_business record) = 1 /\
      Datatypes.length (section_type_code record) = 1 /\
      Datatypes.length (investment_institution_type_code record) = 1 /\
      Datatypes.length (base_price record) = 11 /\
      Datatypes.length (yesterdays_closing_price_type_code record) = 1 /\
      Datatypes.length (yesterdays_closing_price record) = 11 /\
      Datatypes.length (yesterdays_accumulated_trading_amount record) = 12 /\
      Datatypes.length (yesterdays_accumulated_trading_value record) = 22 /\
      Datatypes.length (upper_limit_price record) = 11 /\
      Datatypes.length (lower_limit_price record) = 11 /\
      Datatypes.length (substitute_price_of_securities record) = 11 /\
      Datatypes.length (par_value record) = 11 /\
      Datatypes.length (issuing_price record) = 11 /\
      Datatypes.length (listing_date record) = 8 /\
      Datatypes.length (number_of_listed_shares record) = 16 /\
      Datatypes.length (liquidation_trade record) = 1 /\
      Datatypes.length (the_establishment_date record) = 8 /\
      Datatypes.length (maturity_date record) = 8 /\
      Datatypes.length (exercising_period record) = 8 /\
      Datatypes.length (expiration_date_for_right record) = 8 /\
      Datatypes.length (exercise_price_of_elw_or_bw record) = 13 /\
      Datatypes.length (capital record) = 22 /\
      Datatypes.length (credit_order_possibillity record) = 1 /\
      Datatypes.length (limit_order_permission_type_code record) = 5 /\
      Datatypes.length (market_price_order_permission_type_code record) = 5 /\
      Datatypes.length (conditioned_order_permission_type_code record) = 5 /\
      Datatypes.length (best_favorable_order_permission_type_code record) = 5 /\
      Datatypes.length (first_best_order_permission_type_code record) = 5 /\
      Datatypes.length (mid_price_order_permission_type_code record) = 5 /\
      Datatypes.length (stop_limit_price_order_permission_type_code record) = 5 /\
      Datatypes.length (capital_increase_type_code record) = 2 /\
      Datatypes.length (other_stock_type_code record) = 1 /\
      Datatypes.length (national_stock record) = 1 /\
      Datatypes.length (appraised_price record) = 11 /\
      Datatypes.length (lowest_order_price record) = 11 /\
      Datatypes.length (highest_order_price record) = 11 /\
      Datatypes.length (unit_of_volume_in_main_board record) = 11 /\
      Datatypes.length (lot_size_after_hours_trading record) = 11 /\
      Datatypes.length (rei_ts_type_code record) = 1 /\
      Datatypes.length (target_stock_isin_code record) = 12 /\
      Datatypes.length (currency_iso_code record) = 3 /\
      Datatypes.length (country_code record) = 3 /\
      Datatypes.length (market_making_possibility record) = 1 /\
      Datatypes.length (closing_price_trading_possibility_in_the_after_hours record) = 1 /\
      Datatypes.length (closing_price_trading_in_the_pre_opening_market record) = 1 /\
      Datatypes.length (block_trading_in_the_pre_opening_market record) = 1 /\
      Datatypes.length (basket_trading_in_the_pre_opening_market record) = 1 /\
      Datatypes.length (announcement_of_estimated_trading_price record) = 1 /\
      Datatypes.length (short_selling record) = 1 /\
      Datatypes.length (etf_tracking_difference record) = 13 /\
      Datatypes.length (regs record) = 1 /\
      Datatypes.length (spac record) = 1 /\
      Datatypes.length (tax_type_code record) = 1 /\
      Datatypes.length (appraisal_ratio_of_substitute_price record) = 13 /\
      Datatypes.length (investment_caution_issue record) = 1 /\
      Datatypes.length (delisting_date record) = 8 /\
      Datatypes.length (short_term_overheat_issue_type_code record) = 1 /\
      Datatypes.length (etf_replication_methods_type_code record) = 1 /\
      Datatypes.length (expiration_date record) = 8 /\
      Datatypes.length (distribution_type_code record) = 2 /\
      Datatypes.length (calculation_of_redemption_price_start_date record) = 8 /\
      Datatypes.length (calculation_of_redemption_price_end_date record) = 8 /\
      Datatypes.length (etp_product_type_code record) = 1 /\
      Datatypes.length (index_calculation_institution_type_code record) = 2 /\
      Datatypes.length (index_market_classification_id record) = 6 /\
      Datatypes.length (index_sequence_number record) = 3 /\
      Datatypes.length (tracking_index_leverage_inverse_type_code record) = 2 /\
      Datatypes.length (reference_index_leverage_inverse_type_code record) = 2 /\
      Datatypes.length (index_asset_classification_id_1 record) = 6 /\
      Datatypes.length (index_asset_classification_id_2 record) = 6 /\
      Datatypes.length (ipo_underwriter_member_number record) = 5 /\
      Datatypes.length (lp_order record) = 1 /\
      Datatypes.length (low_liquidity record) = 1 /\
      Datatypes.length (abnormal_rise record) = 1 /\
      Datatypes.length (upper_limit_quantity record) = 23 /\
      Datatypes.length (investment_precaution_issue record) = 1 /\
      Datatypes.length (preferred_stocks_with_lesser_shares record) = 1 /\
      Datatypes.length (spac_merger record) = 1 /\
      Datatypes.length (segment_type_code record) = 1 /\
      Datatypes.length (after_market_possibility record) = 1 /\
      Datatypes.length (pre_market_possibility record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 6 (total_number_of_instruments_of_the_contract record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 9 (abbreviated_issue_code record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name_in_en record) ++
      encode_bytes 5 (group_number record) ++
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 2 (security_group_id record) ++
      encode_bytes 1 (discrete_time_trading record) ++
      encode_bytes 2 (rights_type_code record) ++
      encode_bytes 2 (par_value_type_code record) ++
      encode_bytes 1 (an_issue_of_which_base_price_is_settled_with_a_todays_single_price record) ++
      encode_bytes 2 (reevaluation_reason_code record) ++
      encode_bytes 1 (base_price_change record) ++
      encode_bytes 1 (random_end_trigger_code record) ++
      encode_bytes 1 (market_alert record) ++
      encode_bytes 2 (market_alert_type_code record) ++
      encode_bytes 1 (korea_corporate_governance_stock_price_index_kogi record) ++
      encode_bytes 1 (issue_for_administration record) ++
      encode_bytes 1 (unfaithful_disclosure record) ++
      encode_bytes 1 (back_door_listing record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 10 (industry_id record) ++
      encode_bytes 1 (small_medium_sized_business record) ++
      encode_bytes 1 (section_type_code record) ++
      encode_bytes 1 (investment_institution_type_code record) ++
      encode_bytes 11 (base_price record) ++
      encode_bytes 1 (yesterdays_closing_price_type_code record) ++
      encode_bytes 11 (yesterdays_closing_price record) ++
      encode_bytes 12 (yesterdays_accumulated_trading_amount record) ++
      encode_bytes 22 (yesterdays_accumulated_trading_value record) ++
      encode_bytes 11 (upper_limit_price record) ++
      encode_bytes 11 (lower_limit_price record) ++
      encode_bytes 11 (substitute_price_of_securities record) ++
      encode_bytes 11 (par_value record) ++
      encode_bytes 11 (issuing_price record) ++
      encode_bytes 8 (listing_date record) ++
      encode_bytes 16 (number_of_listed_shares record) ++
      encode_bytes 1 (liquidation_trade record) ++
      encode_bytes 8 (the_establishment_date record) ++
      encode_bytes 8 (maturity_date record) ++
      encode_bytes 8 (exercising_period record) ++
      encode_bytes 8 (expiration_date_for_right record) ++
      encode_bytes 13 (exercise_price_of_elw_or_bw record) ++
      encode_bytes 22 (capital record) ++
      encode_bytes 1 (credit_order_possibillity record) ++
      encode_bytes 5 (limit_order_permission_type_code record) ++
      encode_bytes 5 (market_price_order_permission_type_code record) ++
      encode_bytes 5 (conditioned_order_permission_type_code record) ++
      encode_bytes 5 (best_favorable_order_permission_type_code record) ++
      encode_bytes 5 (first_best_order_permission_type_code record) ++
      encode_bytes 5 (mid_price_order_permission_type_code record) ++
      encode_bytes 5 (stop_limit_price_order_permission_type_code record) ++
      encode_bytes 2 (capital_increase_type_code record) ++
      encode_bytes 1 (other_stock_type_code record) ++
      encode_bytes 1 (national_stock record) ++
      encode_bytes 11 (appraised_price record) ++
      encode_bytes 11 (lowest_order_price record) ++
      encode_bytes 11 (highest_order_price record) ++
      encode_bytes 11 (unit_of_volume_in_main_board record) ++
      encode_bytes 11 (lot_size_after_hours_trading record) ++
      encode_bytes 1 (rei_ts_type_code record) ++
      encode_bytes 12 (target_stock_isin_code record) ++
      encode_bytes 3 (currency_iso_code record) ++
      encode_bytes 3 (country_code record) ++
      encode_bytes 1 (market_making_possibility record) ++
      encode_bytes 1 (closing_price_trading_possibility_in_the_after_hours record) ++
      encode_bytes 1 (closing_price_trading_in_the_pre_opening_market record) ++
      encode_bytes 1 (block_trading_in_the_pre_opening_market record) ++
      encode_bytes 1 (basket_trading_in_the_pre_opening_market record) ++
      encode_bytes 1 (announcement_of_estimated_trading_price record) ++
      encode_bytes 1 (short_selling record) ++
      encode_bytes 13 (etf_tracking_difference record) ++
      encode_bytes 1 (regs record) ++
      encode_bytes 1 (spac record) ++
      encode_bytes 1 (tax_type_code record) ++
      encode_bytes 13 (appraisal_ratio_of_substitute_price record) ++
      encode_bytes 1 (investment_caution_issue record) ++
      encode_bytes 8 (delisting_date record) ++
      encode_bytes 1 (short_term_overheat_issue_type_code record) ++
      encode_bytes 1 (etf_replication_methods_type_code record) ++
      encode_bytes 8 (expiration_date record) ++
      encode_bytes 2 (distribution_type_code record) ++
      encode_bytes 8 (calculation_of_redemption_price_start_date record) ++
      encode_bytes 8 (calculation_of_redemption_price_end_date record) ++
      encode_bytes 1 (etp_product_type_code record) ++
      encode_bytes 2 (index_calculation_institution_type_code record) ++
      encode_bytes 6 (index_market_classification_id record) ++
      encode_bytes 3 (index_sequence_number record) ++
      encode_bytes 2 (tracking_index_leverage_inverse_type_code record) ++
      encode_bytes 2 (reference_index_leverage_inverse_type_code record) ++
      encode_bytes 6 (index_asset_classification_id_1 record) ++
      encode_bytes 6 (index_asset_classification_id_2 record) ++
      encode_bytes 5 (ipo_underwriter_member_number record) ++
      encode_bytes 1 (lp_order record) ++
      encode_bytes 1 (low_liquidity record) ++
      encode_bytes 1 (abnormal_rise record) ++
      encode_bytes 23 (upper_limit_quantity record) ++
      encode_bytes 1 (investment_precaution_issue record) ++
      encode_bytes 1 (preferred_stocks_with_lesser_shares record) ++
      encode_bytes 1 (spac_merger record) ++
      encode_bytes 1 (segment_type_code record) ++
      encode_bytes 1 (after_market_possibility record) ++
      encode_bytes 1 (pre_market_possibility record) ++
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
                              match decode_bytes 40 bytes with
                              | None => None
                              | Some (abbreviated_issue_name_value, bytes) =>
                                  match decode_bytes 40 bytes with
                                  | None => None
                                  | Some (abbreviated_issue_name_in_en_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (group_number_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (market_operation_product_id_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (security_group_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (discrete_time_trading_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (rights_type_code_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (par_value_type_code_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (an_issue_of_which_base_price_is_settled_with_a_todays_single_price_value, bytes) =>
                                                                  match decode_bytes 2 bytes with
                                                                  | None => None
                                                                  | Some (reevaluation_reason_code_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (base_price_change_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (random_end_trigger_code_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (market_alert_value, bytes) =>
                                                                                  match decode_bytes 2 bytes with
                                                                                  | None => None
                                                                                  | Some (market_alert_type_code_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (korea_corporate_governance_stock_price_index_kogi_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (issue_for_administration_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (unfaithful_disclosure_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (back_door_listing_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (trading_halt_value, bytes) =>
                                                                                                          match decode_bytes 10 bytes with
                                                                                                          | None => None
                                                                                                          | Some (industry_id_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (small_medium_sized_business_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (section_type_code_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (investment_institution_type_code_value, bytes) =>
                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (base_price_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (yesterdays_closing_price_type_code_value, bytes) =>
                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (yesterdays_closing_price_value, bytes) =>
                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (yesterdays_accumulated_trading_amount_value, bytes) =>
                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (yesterdays_accumulated_trading_value_value, bytes) =>
                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (upper_limit_price_value, bytes) =>
                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (lower_limit_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (substitute_price_of_securities_value, bytes) =>
                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (par_value_value, bytes) =>
                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (issuing_price_value, bytes) =>
                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (listing_date_value, bytes) =>
                                                                                                                                                                      match decode_bytes 16 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (number_of_listed_shares_value, bytes) =>
                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (liquidation_trade_value, bytes) =>
                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (the_establishment_date_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (maturity_date_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (exercising_period_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (expiration_date_for_right_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (exercise_price_of_elw_or_bw_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (capital_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (credit_order_possibillity_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (limit_order_permission_type_code_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (market_price_order_permission_type_code_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (conditioned_order_permission_type_code_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (best_favorable_order_permission_type_code_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (first_best_order_permission_type_code_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (mid_price_order_permission_type_code_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (stop_limit_price_order_permission_type_code_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (capital_increase_type_code_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (other_stock_type_code_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (national_stock_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (appraised_price_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (lowest_order_price_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (highest_order_price_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (unit_of_volume_in_main_board_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (lot_size_after_hours_trading_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (rei_ts_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (target_stock_isin_code_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (currency_iso_code_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (country_code_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (market_making_possibility_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (closing_price_trading_possibility_in_the_after_hours_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (closing_price_trading_in_the_pre_opening_market_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (block_trading_in_the_pre_opening_market_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (basket_trading_in_the_pre_opening_market_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (announcement_of_estimated_trading_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (short_selling_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (etf_tracking_difference_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (regs_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (spac_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (tax_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (appraisal_ratio_of_substitute_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (investment_caution_issue_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (delisting_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (short_term_overheat_issue_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (etf_replication_methods_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (expiration_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (distribution_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (calculation_of_redemption_price_start_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (calculation_of_redemption_price_end_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                      | Some (etp_product_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                          | Some (index_calculation_institution_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                              | Some (index_market_classification_id_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                  | Some (index_sequence_number_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                      | Some (tracking_index_leverage_inverse_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                          | Some (reference_index_leverage_inverse_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 6 bytes with
                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                              | Some (index_asset_classification_id_1_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                  | Some (index_asset_classification_id_2_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                      | Some (ipo_underwriter_member_number_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                          | Some (lp_order_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                              | Some (low_liquidity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (abnormal_rise_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 23 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (upper_limit_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (investment_precaution_issue_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (preferred_stocks_with_lesser_shares_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (spac_merger_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (segment_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (after_market_possibility_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (pre_market_possibility_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; total_number_of_instruments_of_the_contract := total_number_of_instruments_of_the_contract_value; business_date := business_date_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; abbreviated_issue_code := abbreviated_issue_code_value; abbreviated_issue_name := abbreviated_issue_name_value; abbreviated_issue_name_in_en := abbreviated_issue_name_in_en_value; group_number := group_number_value; market_operation_product_id := market_operation_product_id_value; security_group_id := security_group_id_value; discrete_time_trading := discrete_time_trading_value; rights_type_code := rights_type_code_value; par_value_type_code := par_value_type_code_value; an_issue_of_which_base_price_is_settled_with_a_todays_single_price := an_issue_of_which_base_price_is_settled_with_a_todays_single_price_value; reevaluation_reason_code := reevaluation_reason_code_value; base_price_change := base_price_change_value; random_end_trigger_code := random_end_trigger_code_value; market_alert := market_alert_value; market_alert_type_code := market_alert_type_code_value; korea_corporate_governance_stock_price_index_kogi := korea_corporate_governance_stock_price_index_kogi_value; issue_for_administration := issue_for_administration_value; unfaithful_disclosure := unfaithful_disclosure_value; back_door_listing := back_door_listing_value; trading_halt := trading_halt_value; industry_id := industry_id_value; small_medium_sized_business := small_medium_sized_business_value; section_type_code := section_type_code_value; investment_institution_type_code := investment_institution_type_code_value; base_price := base_price_value; yesterdays_closing_price_type_code := yesterdays_closing_price_type_code_value; yesterdays_closing_price := yesterdays_closing_price_value; yesterdays_accumulated_trading_amount := yesterdays_accumulated_trading_amount_value; yesterdays_accumulated_trading_value := yesterdays_accumulated_trading_value_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; substitute_price_of_securities := substitute_price_of_securities_value; par_value := par_value_value; issuing_price := issuing_price_value; listing_date := listing_date_value; number_of_listed_shares := number_of_listed_shares_value; liquidation_trade := liquidation_trade_value; the_establishment_date := the_establishment_date_value; maturity_date := maturity_date_value; exercising_period := exercising_period_value; expiration_date_for_right := expiration_date_for_right_value; exercise_price_of_elw_or_bw := exercise_price_of_elw_or_bw_value; capital := capital_value; credit_order_possibillity := credit_order_possibillity_value; limit_order_permission_type_code := limit_order_permission_type_code_value; market_price_order_permission_type_code := market_price_order_permission_type_code_value; conditioned_order_permission_type_code := conditioned_order_permission_type_code_value; best_favorable_order_permission_type_code := best_favorable_order_permission_type_code_value; first_best_order_permission_type_code := first_best_order_permission_type_code_value; mid_price_order_permission_type_code := mid_price_order_permission_type_code_value; stop_limit_price_order_permission_type_code := stop_limit_price_order_permission_type_code_value; capital_increase_type_code := capital_increase_type_code_value; other_stock_type_code := other_stock_type_code_value; national_stock := national_stock_value; appraised_price := appraised_price_value; lowest_order_price := lowest_order_price_value; highest_order_price := highest_order_price_value; unit_of_volume_in_main_board := unit_of_volume_in_main_board_value; lot_size_after_hours_trading := lot_size_after_hours_trading_value; rei_ts_type_code := rei_ts_type_code_value; target_stock_isin_code := target_stock_isin_code_value; currency_iso_code := currency_iso_code_value; country_code := country_code_value; market_making_possibility := market_making_possibility_value; closing_price_trading_possibility_in_the_after_hours := closing_price_trading_possibility_in_the_after_hours_value; closing_price_trading_in_the_pre_opening_market := closing_price_trading_in_the_pre_opening_market_value; block_trading_in_the_pre_opening_market := block_trading_in_the_pre_opening_market_value; basket_trading_in_the_pre_opening_market := basket_trading_in_the_pre_opening_market_value; announcement_of_estimated_trading_price := announcement_of_estimated_trading_price_value; short_selling := short_selling_value; etf_tracking_difference := etf_tracking_difference_value; regs := regs_value; spac := spac_value; tax_type_code := tax_type_code_value; appraisal_ratio_of_substitute_price := appraisal_ratio_of_substitute_price_value; investment_caution_issue := investment_caution_issue_value; delisting_date := delisting_date_value; short_term_overheat_issue_type_code := short_term_overheat_issue_type_code_value; etf_replication_methods_type_code := etf_replication_methods_type_code_value; expiration_date := expiration_date_value; distribution_type_code := distribution_type_code_value; calculation_of_redemption_price_start_date := calculation_of_redemption_price_start_date_value; calculation_of_redemption_price_end_date := calculation_of_redemption_price_end_date_value; etp_product_type_code := etp_product_type_code_value; index_calculation_institution_type_code := index_calculation_institution_type_code_value; index_market_classification_id := index_market_classification_id_value; index_sequence_number := index_sequence_number_value; tracking_index_leverage_inverse_type_code := tracking_index_leverage_inverse_type_code_value; reference_index_leverage_inverse_type_code := reference_index_leverage_inverse_type_code_value; index_asset_classification_id_1 := index_asset_classification_id_1_value; index_asset_classification_id_2 := index_asset_classification_id_2_value; ipo_underwriter_member_number := ipo_underwriter_member_number_value; lp_order := lp_order_value; low_liquidity := low_liquidity_value; abnormal_rise := abnormal_rise_value; upper_limit_quantity := upper_limit_quantity_value; investment_precaution_issue := investment_precaution_issue_value; preferred_stocks_with_lesser_shares := preferred_stocks_with_lesser_shares_value; spac_merger := spac_merger_value; segment_type_code := segment_type_code_value; after_market_possibility := after_market_possibility_value; pre_market_possibility := pre_market_possibility_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 627.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 [bound_87 [bound_88 [bound_89 [bound_90 [bound_91 [bound_92 [bound_93 [bound_94 [bound_95 [bound_96 [bound_97 [bound_98 [bound_99 [bound_100 [bound_101 [bound_102 [bound_103 [bound_104 [bound_105 [bound_106 bound_107]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_78.
      rewrite decode_encode_bytes by exact bound_79.
      rewrite decode_encode_bytes by exact bound_80.
      rewrite decode_encode_bytes by exact bound_81.
      rewrite decode_encode_bytes by exact bound_82.
      rewrite decode_encode_bytes by exact bound_83.
      rewrite decode_encode_bytes by exact bound_84.
      rewrite decode_encode_bytes by exact bound_85.
      rewrite decode_encode_bytes by exact bound_86.
      rewrite decode_encode_bytes by exact bound_87.
      rewrite decode_encode_bytes by exact bound_88.
      rewrite decode_encode_bytes by exact bound_89.
      rewrite decode_encode_bytes by exact bound_90.
      rewrite decode_encode_bytes by exact bound_91.
      rewrite decode_encode_bytes by exact bound_92.
      rewrite decode_encode_bytes by exact bound_93.
      rewrite decode_encode_bytes by exact bound_94.
      rewrite decode_encode_bytes by exact bound_95.
      rewrite decode_encode_bytes by exact bound_96.
      rewrite decode_encode_bytes by exact bound_97.
      rewrite decode_encode_bytes by exact bound_98.
      rewrite decode_encode_bytes by exact bound_99.
      rewrite decode_encode_bytes by exact bound_100.
      rewrite decode_encode_bytes by exact bound_101.
      rewrite decode_encode_bytes by exact bound_102.
      rewrite decode_encode_bytes by exact bound_103.
      rewrite decode_encode_bytes by exact bound_104.
      rewrite decode_encode_bytes by exact bound_105.
      rewrite decode_encode_bytes by exact bound_106.
      rewrite decode_encode_uint by exact bound_107.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesEquitiesBatchDataMessage.

  Module SecuritiesClosingDateMessage.

    (** Closing Date reference. Per-issue closing date assignments. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      closing_date : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (closing_date record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 4 (closing_date record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (closing_date_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (end_keyword_value, bytes) =>
                      Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; closing_date := closing_date_value; end_keyword := end_keyword_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesClosingDateMessage.

  Module SecuritiesMmLpInformationMessage.

    (** MM/LP Information. Market maker and liquidity provider assignments per issue. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      market_participant_number : list byte;
      lp_start_date : list byte;
      lp_end_date : list byte;
      minimum_order_volume : list byte;
      maximum_volume_of_multiple_order : list byte;
      bid_ask_spread_unit_code : list byte;
      upper_limit_of_bid_ask_spread : list byte;
      spread_multiple_for_market_holidays : list byte;
      an_obligatory_time_interval_to_place_an_order : list byte;
      minimum_ask_price : list byte;
      maximum_bid_price : list byte;
      minimum_order_price : list byte;
      maximum_order_price : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (market_participant_number record) = 5 /\
      Datatypes.length (lp_start_date record) = 8 /\
      Datatypes.length (lp_end_date record) = 8 /\
      Datatypes.length (minimum_order_volume record) = 11 /\
      Datatypes.length (maximum_volume_of_multiple_order record) = 11 /\
      Datatypes.length (bid_ask_spread_unit_code record) = 1 /\
      Datatypes.length (upper_limit_of_bid_ask_spread record) = 22 /\
      Datatypes.length (spread_multiple_for_market_holidays record) = 11 /\
      Datatypes.length (an_obligatory_time_interval_to_place_an_order record) = 6 /\
      Datatypes.length (minimum_ask_price record) = 22 /\
      Datatypes.length (maximum_bid_price record) = 22 /\
      Datatypes.length (minimum_order_price record) = 22 /\
      Datatypes.length (maximum_order_price record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 5 (market_participant_number record) ++
      encode_bytes 8 (lp_start_date record) ++
      encode_bytes 8 (lp_end_date record) ++
      encode_bytes 11 (minimum_order_volume record) ++
      encode_bytes 11 (maximum_volume_of_multiple_order record) ++
      encode_bytes 1 (bid_ask_spread_unit_code record) ++
      encode_bytes 22 (upper_limit_of_bid_ask_spread record) ++
      encode_bytes 11 (spread_multiple_for_market_holidays record) ++
      encode_bytes 6 (an_obligatory_time_interval_to_place_an_order record) ++
      encode_bytes 22 (minimum_ask_price record) ++
      encode_bytes 22 (maximum_bid_price record) ++
      encode_bytes 22 (minimum_order_price record) ++
      encode_bytes 22 (maximum_order_price record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (market_participant_number_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (lp_start_date_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (lp_end_date_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (minimum_order_volume_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (maximum_volume_of_multiple_order_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (bid_ask_spread_unit_code_value, bytes) =>
                                      match decode_bytes 22 bytes with
                                      | None => None
                                      | Some (upper_limit_of_bid_ask_spread_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (spread_multiple_for_market_holidays_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (an_obligatory_time_interval_to_place_an_order_value, bytes) =>
                                                  match decode_bytes 22 bytes with
                                                  | None => None
                                                  | Some (minimum_ask_price_value, bytes) =>
                                                      match decode_bytes 22 bytes with
                                                      | None => None
                                                      | Some (maximum_bid_price_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (minimum_order_price_value, bytes) =>
                                                              match decode_bytes 22 bytes with
                                                              | None => None
                                                              | Some (maximum_order_price_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; market_participant_number := market_participant_number_value; lp_start_date := lp_start_date_value; lp_end_date := lp_end_date_value; minimum_order_volume := minimum_order_volume_value; maximum_volume_of_multiple_order := maximum_volume_of_multiple_order_value; bid_ask_spread_unit_code := bid_ask_spread_unit_code_value; upper_limit_of_bid_ask_spread := upper_limit_of_bid_ask_spread_value; spread_multiple_for_market_holidays := spread_multiple_for_market_holidays_value; an_obligatory_time_interval_to_place_an_order := an_obligatory_time_interval_to_place_an_order_value; minimum_ask_price := minimum_ask_price_value; maximum_bid_price := maximum_bid_price_value; minimum_order_price := minimum_order_price_value; maximum_order_price := maximum_order_price_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 192.
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

  End SecuritiesMmLpInformationMessage.

  Module SecuritiesMemberInformationMessage.

    (** Member firm information reference data (IFMSBTD0012) — Securities C STK variant. *)
    Record t := {
      message_sequence_number : list byte;
      business_date : list byte;
      market_participant_number : list byte;
      name_of_a_market_participant_in_kr : list byte;
      name_of_a_market_participant_in_en : list byte;
      an_abbreviated_name_of_a_market_participant_in_kr : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (market_participant_number record) = 5 /\
      Datatypes.length (name_of_a_market_participant_in_kr record) = 80 /\
      Datatypes.length (name_of_a_market_participant_in_en record) = 80 /\
      Datatypes.length (an_abbreviated_name_of_a_market_participant_in_kr record) = 20 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 5 (market_participant_number record) ++
      encode_bytes 80 (name_of_a_market_participant_in_kr record) ++
      encode_bytes 80 (name_of_a_market_participant_in_en record) ++
      encode_bytes 20 (an_abbreviated_name_of_a_market_participant_in_kr record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (business_date_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (market_participant_number_value, bytes) =>
                  match decode_bytes 80 bytes with
                  | None => None
                  | Some (name_of_a_market_participant_in_kr_value, bytes) =>
                      match decode_bytes 80 bytes with
                      | None => None
                      | Some (name_of_a_market_participant_in_en_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (an_abbreviated_name_of_a_market_participant_in_kr_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| message_sequence_number := message_sequence_number_value; business_date := business_date_value; market_participant_number := market_participant_number_value; name_of_a_market_participant_in_kr := name_of_a_market_participant_in_kr_value; name_of_a_market_participant_in_en := name_of_a_market_participant_in_en_value; an_abbreviated_name_of_a_market_participant_in_kr := an_abbreviated_name_of_a_market_participant_in_kr_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 202.
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

  End SecuritiesMemberInformationMessage.

  Module SecuritiesTreasuryStocksBatchMessage.

    (** Treasury Stocks Batch reference data. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      treasury_stock_report_id : list byte;
      treasury_stock_ask_bid_type_code : list byte;
      treasury_stock_application_date : list byte;
      treasury_stock_trading_start_date : list byte;
      treasury_stock_trading_end_date : list byte;
      trearsury_stock_trading_method_type_code : list byte;
      market_participant_number : list byte;
      buying_volume_open_single_price_session : list byte;
      buying_volume_regular_session : list byte;
      buying_volume_block_trading_in_off_hours_session : list byte;
      accumulated_trading_quantity : list byte;
      accumulated_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (treasury_stock_report_id record) = 5 /\
      Datatypes.length (treasury_stock_ask_bid_type_code record) = 1 /\
      Datatypes.length (treasury_stock_application_date record) = 8 /\
      Datatypes.length (treasury_stock_trading_start_date record) = 8 /\
      Datatypes.length (treasury_stock_trading_end_date record) = 8 /\
      Datatypes.length (trearsury_stock_trading_method_type_code record) = 1 /\
      Datatypes.length (market_participant_number record) = 5 /\
      Datatypes.length (buying_volume_open_single_price_session record) = 12 /\
      Datatypes.length (buying_volume_regular_session record) = 12 /\
      Datatypes.length (buying_volume_block_trading_in_off_hours_session record) = 12 /\
      Datatypes.length (accumulated_trading_quantity record) = 15 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 5 (treasury_stock_report_id record) ++
      encode_bytes 1 (treasury_stock_ask_bid_type_code record) ++
      encode_bytes 8 (treasury_stock_application_date record) ++
      encode_bytes 8 (treasury_stock_trading_start_date record) ++
      encode_bytes 8 (treasury_stock_trading_end_date record) ++
      encode_bytes 1 (trearsury_stock_trading_method_type_code record) ++
      encode_bytes 5 (market_participant_number record) ++
      encode_bytes 12 (buying_volume_open_single_price_session record) ++
      encode_bytes 12 (buying_volume_regular_session record) ++
      encode_bytes 12 (buying_volume_block_trading_in_off_hours_session record) ++
      encode_bytes 15 (accumulated_trading_quantity record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (treasury_stock_report_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (treasury_stock_ask_bid_type_code_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (treasury_stock_application_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (treasury_stock_trading_start_date_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (treasury_stock_trading_end_date_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trearsury_stock_trading_method_type_code_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (market_participant_number_value, bytes) =>
                                          match decode_bytes 12 bytes with
                                          | None => None
                                          | Some (buying_volume_open_single_price_session_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (buying_volume_regular_session_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (buying_volume_block_trading_in_off_hours_session_value, bytes) =>
                                                      match decode_bytes 15 bytes with
                                                      | None => None
                                                      | Some (accumulated_trading_quantity_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_value_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (end_keyword_value, bytes) =>
                                                                  Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; treasury_stock_report_id := treasury_stock_report_id_value; treasury_stock_ask_bid_type_code := treasury_stock_ask_bid_type_code_value; treasury_stock_application_date := treasury_stock_application_date_value; treasury_stock_trading_start_date := treasury_stock_trading_start_date_value; treasury_stock_trading_end_date := treasury_stock_trading_end_date_value; trearsury_stock_trading_method_type_code := trearsury_stock_trading_method_type_code_value; market_participant_number := market_participant_number_value; buying_volume_open_single_price_session := buying_volume_open_single_price_session_value; buying_volume_regular_session := buying_volume_regular_session_value; buying_volume_block_trading_in_off_hours_session := buying_volume_block_trading_in_off_hours_session_value; accumulated_trading_quantity := accumulated_trading_quantity_value; accumulated_trading_value := accumulated_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 130.
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

  End SecuritiesTreasuryStocksBatchMessage.

  Module SecuritiesEquityIndexIndicatorMessage.

    (** Equity Index Indicator. Real-time index value indicators for equity-derivatives underlying. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      security_group_id : list byte;
      eps_calculation : list byte;
      eps : list byte;
      loss_category : list byte;
      per : list byte;
      bps_calculation : list byte;
      bps : list byte;
      pbr : list byte;
      dps_calculation : list byte;
      dps : list byte;
      dividend_yield : list byte;
      market_capitalization_type_code : list byte;
      filler_1 : list byte;
      index_classification_level_1 : list byte;
      index_classification_level_2 : list byte;
      index_classification_level_3 : list byte;
      kospi_200_sector_code_1 : list byte;
      kospi_200_sector_code_2 : list byte;
      kospi : list byte;
      kosdaq : list byte;
      kospi_100 : list byte;
      kospi_50 : list byte;
      kosdaq_150 : list byte;
      krx_100 : list byte;
      krx_300 : list byte;
      kospi_200_high_dividend_yield_index : list byte;
      krx_bbig_index : list byte;
      krx_secondary_battery_top_10_index : list byte;
      krx_bio_top_10_index : list byte;
      korea_value_up_index : list byte;
      filler_8 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (security_group_id record) = 2 /\
      Datatypes.length (eps_calculation record) = 1 /\
      Datatypes.length (eps record) = 22 /\
      Datatypes.length (loss_category record) = 1 /\
      Datatypes.length (per record) = 13 /\
      Datatypes.length (bps_calculation record) = 1 /\
      Datatypes.length (bps record) = 22 /\
      Datatypes.length (pbr record) = 13 /\
      Datatypes.length (dps_calculation record) = 1 /\
      Datatypes.length (dps record) = 22 /\
      Datatypes.length (dividend_yield record) = 13 /\
      Datatypes.length (market_capitalization_type_code record) = 1 /\
      Datatypes.length (filler_1 record) = 1 /\
      Datatypes.length (index_classification_level_1 record) = 6 /\
      Datatypes.length (index_classification_level_2 record) = 6 /\
      Datatypes.length (index_classification_level_3 record) = 6 /\
      Datatypes.length (kospi_200_sector_code_1 record) = 1 /\
      Datatypes.length (kospi_200_sector_code_2 record) = 1 /\
      Datatypes.length (kospi record) = 1 /\
      Datatypes.length (kosdaq record) = 1 /\
      Datatypes.length (kospi_100 record) = 1 /\
      Datatypes.length (kospi_50 record) = 1 /\
      Datatypes.length (kosdaq_150 record) = 1 /\
      Datatypes.length (krx_100 record) = 1 /\
      Datatypes.length (krx_300 record) = 1 /\
      Datatypes.length (kospi_200_high_dividend_yield_index record) = 1 /\
      Datatypes.length (krx_bbig_index record) = 1 /\
      Datatypes.length (krx_secondary_battery_top_10_index record) = 1 /\
      Datatypes.length (krx_bio_top_10_index record) = 1 /\
      Datatypes.length (korea_value_up_index record) = 1 /\
      Datatypes.length (filler_8 record) = 8 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 2 (security_group_id record) ++
      encode_bytes 1 (eps_calculation record) ++
      encode_bytes 22 (eps record) ++
      encode_bytes 1 (loss_category record) ++
      encode_bytes 13 (per record) ++
      encode_bytes 1 (bps_calculation record) ++
      encode_bytes 22 (bps record) ++
      encode_bytes 13 (pbr record) ++
      encode_bytes 1 (dps_calculation record) ++
      encode_bytes 22 (dps record) ++
      encode_bytes 13 (dividend_yield record) ++
      encode_bytes 1 (market_capitalization_type_code record) ++
      encode_bytes 1 (filler_1 record) ++
      encode_bytes 6 (index_classification_level_1 record) ++
      encode_bytes 6 (index_classification_level_2 record) ++
      encode_bytes 6 (index_classification_level_3 record) ++
      encode_bytes 1 (kospi_200_sector_code_1 record) ++
      encode_bytes 1 (kospi_200_sector_code_2 record) ++
      encode_bytes 1 (kospi record) ++
      encode_bytes 1 (kosdaq record) ++
      encode_bytes 1 (kospi_100 record) ++
      encode_bytes 1 (kospi_50 record) ++
      encode_bytes 1 (kosdaq_150 record) ++
      encode_bytes 1 (krx_100 record) ++
      encode_bytes 1 (krx_300 record) ++
      encode_bytes 1 (kospi_200_high_dividend_yield_index record) ++
      encode_bytes 1 (krx_bbig_index record) ++
      encode_bytes 1 (krx_secondary_battery_top_10_index record) ++
      encode_bytes 1 (krx_bio_top_10_index record) ++
      encode_bytes 1 (korea_value_up_index record) ++
      encode_bytes 8 (filler_8 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (a_designated_number_for_an_issue_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (security_group_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (eps_calculation_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (eps_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (loss_category_value, bytes) =>
                                  match decode_bytes 13 bytes with
                                  | None => None
                                  | Some (per_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (bps_calculation_value, bytes) =>
                                          match decode_bytes 22 bytes with
                                          | None => None
                                          | Some (bps_value, bytes) =>
                                              match decode_bytes 13 bytes with
                                              | None => None
                                              | Some (pbr_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (dps_calculation_value, bytes) =>
                                                      match decode_bytes 22 bytes with
                                                      | None => None
                                                      | Some (dps_value, bytes) =>
                                                          match decode_bytes 13 bytes with
                                                          | None => None
                                                          | Some (dividend_yield_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (market_capitalization_type_code_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (filler_1_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (index_classification_level_1_value, bytes) =>
                                                                          match decode_bytes 6 bytes with
                                                                          | None => None
                                                                          | Some (index_classification_level_2_value, bytes) =>
                                                                              match decode_bytes 6 bytes with
                                                                              | None => None
                                                                              | Some (index_classification_level_3_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (kospi_200_sector_code_1_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (kospi_200_sector_code_2_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (kospi_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (kosdaq_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (kospi_100_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (kospi_50_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (kosdaq_150_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (krx_100_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (krx_300_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (kospi_200_high_dividend_yield_index_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (krx_bbig_index_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (krx_secondary_battery_top_10_index_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (krx_bio_top_10_index_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (korea_value_up_index_value, bytes) =>
                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (filler_8_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; security_group_id := security_group_id_value; eps_calculation := eps_calculation_value; eps := eps_value; loss_category := loss_category_value; per := per_value; bps_calculation := bps_calculation_value; bps := bps_value; pbr := pbr_value; dps_calculation := dps_calculation_value; dps := dps_value; dividend_yield := dividend_yield_value; market_capitalization_type_code := market_capitalization_type_code_value; filler_1 := filler_1_value; index_classification_level_1 := index_classification_level_1_value; index_classification_level_2 := index_classification_level_2_value; index_classification_level_3 := index_classification_level_3_value; kospi_200_sector_code_1 := kospi_200_sector_code_1_value; kospi_200_sector_code_2 := kospi_200_sector_code_2_value; kospi := kospi_value; kosdaq := kosdaq_value; kospi_100 := kospi_100_value; kospi_50 := kospi_50_value; kosdaq_150 := kosdaq_150_value; krx_100 := krx_100_value; krx_300 := krx_300_value; kospi_200_high_dividend_yield_index := kospi_200_high_dividend_yield_index_value; krx_bbig_index := krx_bbig_index_value; krx_secondary_battery_top_10_index := krx_secondary_battery_top_10_index_value; krx_bio_top_10_index := krx_bio_top_10_index_value; korea_value_up_index := korea_value_up_index_value; filler_8 := filler_8_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 180.
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

  End SecuritiesEquityIndexIndicatorMessage.

  Module SecuritiesDividendYieldPerIndustryMessage.

    (** Dividend Yield per Industry reference (IFMSBTD0003) — KOSPI variant. *)
    Record t := {
      message_sequence_number : list byte;
      index_id : list byte;
      dividend_yield : list byte;
      filler_3 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (dividend_yield record) = 13 /\
      Datatypes.length (filler_3 record) = 3 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 13 (dividend_yield record) ++
      encode_bytes 3 (filler_3 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (index_id_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (dividend_yield_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (filler_3_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| message_sequence_number := message_sequence_number_value; index_id := index_id_value; dividend_yield := dividend_yield_value; filler_3 := filler_3_value; end_keyword := end_keyword_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesDividendYieldPerIndustryMessage.

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

  Module SecuritiesElwBatchDataMessage.

    (** ELW Batch Data. Per-issue reference data for Equity Linked Warrants. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      name_of_issuer : list byte;
      english_name_of_issuer : list byte;
      numbers_of_issuer : list byte;
      market_id_1_for_underlying_assets_indices : list byte;
      market_id_2_for_underlying_assets_indices : list byte;
      market_id_3_for_underlying_assets_indices : list byte;
      market_id_4_for_underlying_assets_indices : list byte;
      market_id_5_for_underlying_assets_indices : list byte;
      underlying_asset_type_code_1 : list byte;
      underlying_asset_type_code_2 : list byte;
      underlying_asset_type_code_3 : list byte;
      underlying_asset_type_code_4 : list byte;
      underlying_asset_type_code_5 : list byte;
      underlying_asset_composition_ratio_1 : list byte;
      underlying_asset_composition_ratio_2 : list byte;
      underlying_asset_composition_ratio_3 : list byte;
      underlying_asset_composition_ratio_4 : list byte;
      underlying_asset_composition_ratio_5 : list byte;
      index_id : list byte;
      option_rights_type_code : list byte;
      rights_execution_type_code : list byte;
      payment_methods : list byte;
      last_trading_date : list byte;
      elw_payment_date : list byte;
      base_price_of_underlying_asset : list byte;
      details_of_rights : list byte;
      elw_conversion_rate : list byte;
      elw_guaranteed_rate_for_price_increases : list byte;
      elw_guaranteed_rate_for_price_decreases : list byte;
      elw_fixed_payment : list byte;
      elw_payment_agent : list byte;
      calculation_methods_of_appraised_price_at_maturity : list byte;
      elw_rights_type_code : list byte;
      elw_lp_holding_quantity : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (name_of_issuer record) = 80 /\
      Datatypes.length (english_name_of_issuer record) = 80 /\
      Datatypes.length (numbers_of_issuer record) = 5 /\
      Datatypes.length (market_id_1_for_underlying_assets_indices record) = 3 /\
      Datatypes.length (market_id_2_for_underlying_assets_indices record) = 3 /\
      Datatypes.length (market_id_3_for_underlying_assets_indices record) = 3 /\
      Datatypes.length (market_id_4_for_underlying_assets_indices record) = 3 /\
      Datatypes.length (market_id_5_for_underlying_assets_indices record) = 3 /\
      Datatypes.length (underlying_asset_type_code_1 record) = 12 /\
      Datatypes.length (underlying_asset_type_code_2 record) = 12 /\
      Datatypes.length (underlying_asset_type_code_3 record) = 12 /\
      Datatypes.length (underlying_asset_type_code_4 record) = 12 /\
      Datatypes.length (underlying_asset_type_code_5 record) = 12 /\
      Datatypes.length (underlying_asset_composition_ratio_1 record) = 13 /\
      Datatypes.length (underlying_asset_composition_ratio_2 record) = 13 /\
      Datatypes.length (underlying_asset_composition_ratio_3 record) = 13 /\
      Datatypes.length (underlying_asset_composition_ratio_4 record) = 13 /\
      Datatypes.length (underlying_asset_composition_ratio_5 record) = 13 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (option_rights_type_code record) = 1 /\
      Datatypes.length (rights_execution_type_code record) = 1 /\
      Datatypes.length (payment_methods record) = 1 /\
      Datatypes.length (last_trading_date record) = 8 /\
      Datatypes.length (elw_payment_date record) = 8 /\
      Datatypes.length (base_price_of_underlying_asset record) = 13 /\
      Datatypes.length (details_of_rights record) = 200 /\
      Datatypes.length (elw_conversion_rate record) = 13 /\
      Datatypes.length (elw_guaranteed_rate_for_price_increases record) = 10 /\
      Datatypes.length (elw_guaranteed_rate_for_price_decreases record) = 10 /\
      Datatypes.length (elw_fixed_payment record) = 22 /\
      Datatypes.length (elw_payment_agent record) = 80 /\
      Datatypes.length (calculation_methods_of_appraised_price_at_maturity record) = 200 /\
      Datatypes.length (elw_rights_type_code record) = 1 /\
      Datatypes.length (elw_lp_holding_quantity record) = 15 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 80 (name_of_issuer record) ++
      encode_bytes 80 (english_name_of_issuer record) ++
      encode_bytes 5 (numbers_of_issuer record) ++
      encode_bytes 3 (market_id_1_for_underlying_assets_indices record) ++
      encode_bytes 3 (market_id_2_for_underlying_assets_indices record) ++
      encode_bytes 3 (market_id_3_for_underlying_assets_indices record) ++
      encode_bytes 3 (market_id_4_for_underlying_assets_indices record) ++
      encode_bytes 3 (market_id_5_for_underlying_assets_indices record) ++
      encode_bytes 12 (underlying_asset_type_code_1 record) ++
      encode_bytes 12 (underlying_asset_type_code_2 record) ++
      encode_bytes 12 (underlying_asset_type_code_3 record) ++
      encode_bytes 12 (underlying_asset_type_code_4 record) ++
      encode_bytes 12 (underlying_asset_type_code_5 record) ++
      encode_bytes 13 (underlying_asset_composition_ratio_1 record) ++
      encode_bytes 13 (underlying_asset_composition_ratio_2 record) ++
      encode_bytes 13 (underlying_asset_composition_ratio_3 record) ++
      encode_bytes 13 (underlying_asset_composition_ratio_4 record) ++
      encode_bytes 13 (underlying_asset_composition_ratio_5 record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 1 (option_rights_type_code record) ++
      encode_bytes 1 (rights_execution_type_code record) ++
      encode_bytes 1 (payment_methods record) ++
      encode_bytes 8 (last_trading_date record) ++
      encode_bytes 8 (elw_payment_date record) ++
      encode_bytes 13 (base_price_of_underlying_asset record) ++
      encode_bytes 200 (details_of_rights record) ++
      encode_bytes 13 (elw_conversion_rate record) ++
      encode_bytes 10 (elw_guaranteed_rate_for_price_increases record) ++
      encode_bytes 10 (elw_guaranteed_rate_for_price_decreases record) ++
      encode_bytes 22 (elw_fixed_payment record) ++
      encode_bytes 80 (elw_payment_agent record) ++
      encode_bytes 200 (calculation_methods_of_appraised_price_at_maturity record) ++
      encode_bytes 1 (elw_rights_type_code record) ++
      encode_bytes 15 (elw_lp_holding_quantity record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (a_designated_number_for_an_issue_value, bytes) =>
                  match decode_bytes 80 bytes with
                  | None => None
                  | Some (name_of_issuer_value, bytes) =>
                      match decode_bytes 80 bytes with
                      | None => None
                      | Some (english_name_of_issuer_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (numbers_of_issuer_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (market_id_1_for_underlying_assets_indices_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (market_id_2_for_underlying_assets_indices_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (market_id_3_for_underlying_assets_indices_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (market_id_4_for_underlying_assets_indices_value, bytes) =>
                                              match decode_bytes 3 bytes with
                                              | None => None
                                              | Some (market_id_5_for_underlying_assets_indices_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (underlying_asset_type_code_1_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (underlying_asset_type_code_2_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (underlying_asset_type_code_3_value, bytes) =>
                                                              match decode_bytes 12 bytes with
                                                              | None => None
                                                              | Some (underlying_asset_type_code_4_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (underlying_asset_type_code_5_value, bytes) =>
                                                                      match decode_bytes 13 bytes with
                                                                      | None => None
                                                                      | Some (underlying_asset_composition_ratio_1_value, bytes) =>
                                                                          match decode_bytes 13 bytes with
                                                                          | None => None
                                                                          | Some (underlying_asset_composition_ratio_2_value, bytes) =>
                                                                              match decode_bytes 13 bytes with
                                                                              | None => None
                                                                              | Some (underlying_asset_composition_ratio_3_value, bytes) =>
                                                                                  match decode_bytes 13 bytes with
                                                                                  | None => None
                                                                                  | Some (underlying_asset_composition_ratio_4_value, bytes) =>
                                                                                      match decode_bytes 13 bytes with
                                                                                      | None => None
                                                                                      | Some (underlying_asset_composition_ratio_5_value, bytes) =>
                                                                                          match decode_bytes 6 bytes with
                                                                                          | None => None
                                                                                          | Some (index_id_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (option_rights_type_code_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (rights_execution_type_code_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (payment_methods_value, bytes) =>
                                                                                                          match decode_bytes 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (last_trading_date_value, bytes) =>
                                                                                                              match decode_bytes 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (elw_payment_date_value, bytes) =>
                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (base_price_of_underlying_asset_value, bytes) =>
                                                                                                                      match decode_bytes 200 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (details_of_rights_value, bytes) =>
                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (elw_conversion_rate_value, bytes) =>
                                                                                                                              match decode_bytes 10 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (elw_guaranteed_rate_for_price_increases_value, bytes) =>
                                                                                                                                  match decode_bytes 10 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (elw_guaranteed_rate_for_price_decreases_value, bytes) =>
                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (elw_fixed_payment_value, bytes) =>
                                                                                                                                          match decode_bytes 80 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (elw_payment_agent_value, bytes) =>
                                                                                                                                              match decode_bytes 200 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (calculation_methods_of_appraised_price_at_maturity_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (elw_rights_type_code_value, bytes) =>
                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (elw_lp_holding_quantity_value, bytes) =>
                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (filler_4_value, bytes) =>
                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; name_of_issuer := name_of_issuer_value; english_name_of_issuer := english_name_of_issuer_value; numbers_of_issuer := numbers_of_issuer_value; market_id_1_for_underlying_assets_indices := market_id_1_for_underlying_assets_indices_value; market_id_2_for_underlying_assets_indices := market_id_2_for_underlying_assets_indices_value; market_id_3_for_underlying_assets_indices := market_id_3_for_underlying_assets_indices_value; market_id_4_for_underlying_assets_indices := market_id_4_for_underlying_assets_indices_value; market_id_5_for_underlying_assets_indices := market_id_5_for_underlying_assets_indices_value; underlying_asset_type_code_1 := underlying_asset_type_code_1_value; underlying_asset_type_code_2 := underlying_asset_type_code_2_value; underlying_asset_type_code_3 := underlying_asset_type_code_3_value; underlying_asset_type_code_4 := underlying_asset_type_code_4_value; underlying_asset_type_code_5 := underlying_asset_type_code_5_value; underlying_asset_composition_ratio_1 := underlying_asset_composition_ratio_1_value; underlying_asset_composition_ratio_2 := underlying_asset_composition_ratio_2_value; underlying_asset_composition_ratio_3 := underlying_asset_composition_ratio_3_value; underlying_asset_composition_ratio_4 := underlying_asset_composition_ratio_4_value; underlying_asset_composition_ratio_5 := underlying_asset_composition_ratio_5_value; index_id := index_id_value; option_rights_type_code := option_rights_type_code_value; rights_execution_type_code := rights_execution_type_code_value; payment_methods := payment_methods_value; last_trading_date := last_trading_date_value; elw_payment_date := elw_payment_date_value; base_price_of_underlying_asset := base_price_of_underlying_asset_value; details_of_rights := details_of_rights_value; elw_conversion_rate := elw_conversion_rate_value; elw_guaranteed_rate_for_price_increases := elw_guaranteed_rate_for_price_increases_value; elw_guaranteed_rate_for_price_decreases := elw_guaranteed_rate_for_price_decreases_value; elw_fixed_payment := elw_fixed_payment_value; elw_payment_agent := elw_payment_agent_value; calculation_methods_of_appraised_price_at_maturity := calculation_methods_of_appraised_price_at_maturity_value; elw_rights_type_code := elw_rights_type_code_value; elw_lp_holding_quantity := elw_lp_holding_quantity_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 925.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 bound_38]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_38.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesElwBatchDataMessage.

  Module SecuritiesEtnBatchDataMessage.

    (** ETN Batch Data. Per-issue reference data for Exchange Traded Notes. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      name_of_issuer : list byte;
      english_name_of_issuer : list byte;
      numbers_of_issuer : list byte;
      payment_methods : list byte;
      last_trading_date : list byte;
      etn_payment_date : list byte;
      etn_lp_holding_quantity : list byte;
      loss_protection_etn_profit_structure_code : list byte;
      etn_maximum_redemption_price : list byte;
      etn_minimum_redemption_price : list byte;
      etn_early_redemption_possibility : list byte;
      etn_early_redemption_period : list byte;
      institution_code_1_appraised_price_calculation : list byte;
      institution_code_2_appraised_price_calculation : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (name_of_issuer record) = 80 /\
      Datatypes.length (english_name_of_issuer record) = 80 /\
      Datatypes.length (numbers_of_issuer record) = 5 /\
      Datatypes.length (payment_methods record) = 1 /\
      Datatypes.length (last_trading_date record) = 8 /\
      Datatypes.length (etn_payment_date record) = 8 /\
      Datatypes.length (etn_lp_holding_quantity record) = 15 /\
      Datatypes.length (loss_protection_etn_profit_structure_code record) = 2 /\
      Datatypes.length (etn_maximum_redemption_price record) = 11 /\
      Datatypes.length (etn_minimum_redemption_price record) = 11 /\
      Datatypes.length (etn_early_redemption_possibility record) = 1 /\
      Datatypes.length (etn_early_redemption_period record) = 2 /\
      Datatypes.length (institution_code_1_appraised_price_calculation record) = 2 /\
      Datatypes.length (institution_code_2_appraised_price_calculation record) = 2 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 80 (name_of_issuer record) ++
      encode_bytes 80 (english_name_of_issuer record) ++
      encode_bytes 5 (numbers_of_issuer record) ++
      encode_bytes 1 (payment_methods record) ++
      encode_bytes 8 (last_trading_date record) ++
      encode_bytes 8 (etn_payment_date record) ++
      encode_bytes 15 (etn_lp_holding_quantity record) ++
      encode_bytes 2 (loss_protection_etn_profit_structure_code record) ++
      encode_bytes 11 (etn_maximum_redemption_price record) ++
      encode_bytes 11 (etn_minimum_redemption_price record) ++
      encode_bytes 1 (etn_early_redemption_possibility record) ++
      encode_bytes 2 (etn_early_redemption_period record) ++
      encode_bytes 2 (institution_code_1_appraised_price_calculation record) ++
      encode_bytes 2 (institution_code_2_appraised_price_calculation record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (a_designated_number_for_an_issue_value, bytes) =>
                  match decode_bytes 80 bytes with
                  | None => None
                  | Some (name_of_issuer_value, bytes) =>
                      match decode_bytes 80 bytes with
                      | None => None
                      | Some (english_name_of_issuer_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (numbers_of_issuer_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (payment_methods_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (last_trading_date_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (etn_payment_date_value, bytes) =>
                                          match decode_bytes 15 bytes with
                                          | None => None
                                          | Some (etn_lp_holding_quantity_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (loss_protection_etn_profit_structure_code_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (etn_maximum_redemption_price_value, bytes) =>
                                                      match decode_bytes 11 bytes with
                                                      | None => None
                                                      | Some (etn_minimum_redemption_price_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (etn_early_redemption_possibility_value, bytes) =>
                                                              match decode_bytes 2 bytes with
                                                              | None => None
                                                              | Some (etn_early_redemption_period_value, bytes) =>
                                                                  match decode_bytes 2 bytes with
                                                                  | None => None
                                                                  | Some (institution_code_1_appraised_price_calculation_value, bytes) =>
                                                                      match decode_bytes 2 bytes with
                                                                      | None => None
                                                                      | Some (institution_code_2_appraised_price_calculation_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (end_keyword_value, bytes) =>
                                                                              Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; name_of_issuer := name_of_issuer_value; english_name_of_issuer := english_name_of_issuer_value; numbers_of_issuer := numbers_of_issuer_value; payment_methods := payment_methods_value; last_trading_date := last_trading_date_value; etn_payment_date := etn_payment_date_value; etn_lp_holding_quantity := etn_lp_holding_quantity_value; loss_protection_etn_profit_structure_code := loss_protection_etn_profit_structure_code_value; etn_maximum_redemption_price := etn_maximum_redemption_price_value; etn_minimum_redemption_price := etn_minimum_redemption_price_value; etn_early_redemption_possibility := etn_early_redemption_possibility_value; etn_early_redemption_period := etn_early_redemption_period_value; institution_code_1_appraised_price_calculation := institution_code_1_appraised_price_calculation_value; institution_code_2_appraised_price_calculation := institution_code_2_appraised_price_calculation_value; end_keyword := end_keyword_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 255.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesEtnBatchDataMessage.

  Module SecuritiesEtnEarlyRedemptionMessage.

    (** ETN Early Redemption Criteria reference. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      etn_early_redemption_period : list byte;
      early_redemption_appraisal_date : list byte;
      early_redemption_criteria_code : list byte;
      early_redemption_base_index_1 : list byte;
      early_redemption_base_index_2 : list byte;
      early_redemption_price : list byte;
      early_repemption_payment_date : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (etn_early_redemption_period record) = 2 /\
      Datatypes.length (early_redemption_appraisal_date record) = 8 /\
      Datatypes.length (early_redemption_criteria_code record) = 1 /\
      Datatypes.length (early_redemption_base_index_1 record) = 10 /\
      Datatypes.length (early_redemption_base_index_2 record) = 10 /\
      Datatypes.length (early_redemption_price record) = 23 /\
      Datatypes.length (early_repemption_payment_date record) = 8 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 2 (etn_early_redemption_period record) ++
      encode_bytes 8 (early_redemption_appraisal_date record) ++
      encode_bytes 1 (early_redemption_criteria_code record) ++
      encode_bytes 10 (early_redemption_base_index_1 record) ++
      encode_bytes 10 (early_redemption_base_index_2 record) ++
      encode_bytes 23 (early_redemption_price record) ++
      encode_bytes 8 (early_repemption_payment_date record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (etn_early_redemption_period_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (early_redemption_appraisal_date_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (early_redemption_criteria_code_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (early_redemption_base_index_1_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (early_redemption_base_index_2_value, bytes) =>
                                  match decode_bytes 23 bytes with
                                  | None => None
                                  | Some (early_redemption_price_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (early_repemption_payment_date_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; etn_early_redemption_period := etn_early_redemption_period_value; early_redemption_appraisal_date := early_redemption_appraisal_date_value; early_redemption_criteria_code := early_redemption_criteria_code_value; early_redemption_base_index_1 := early_redemption_base_index_1_value; early_redemption_base_index_2 := early_redemption_base_index_2_value; early_redemption_price := early_redemption_price_value; early_repemption_payment_date := early_repemption_payment_date_value; end_keyword := end_keyword_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 83.
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

  End SecuritiesEtnEarlyRedemptionMessage.

  Module SecuritiesEtpConstituentsMessage.

    (** ETP Constituents reference (IFMSBTD0013) — Securities C STK variant. *)
    Record t := {
      message_sequence_number : list byte;
      index_calculation_institution_type_code : list byte;
      index_market_classification_id : list byte;
      index_sequence_number : list byte;
      index_leverage_inverse_type_code : list byte;
      index_name : list byte;
      index_name_in_en : list byte;
      index_asset_classification_id_1 : list byte;
      index_asset_classification_id_2 : list byte;
      index_id : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (index_calculation_institution_type_code record) = 2 /\
      Datatypes.length (index_market_classification_id record) = 6 /\
      Datatypes.length (index_sequence_number record) = 3 /\
      Datatypes.length (index_leverage_inverse_type_code record) = 2 /\
      Datatypes.length (index_name record) = 80 /\
      Datatypes.length (index_name_in_en record) = 80 /\
      Datatypes.length (index_asset_classification_id_1 record) = 6 /\
      Datatypes.length (index_asset_classification_id_2 record) = 6 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (index_calculation_institution_type_code record) ++
      encode_bytes 6 (index_market_classification_id record) ++
      encode_bytes 3 (index_sequence_number record) ++
      encode_bytes 2 (index_leverage_inverse_type_code record) ++
      encode_bytes 80 (index_name record) ++
      encode_bytes 80 (index_name_in_en record) ++
      encode_bytes 6 (index_asset_classification_id_1 record) ++
      encode_bytes 6 (index_asset_classification_id_2 record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (index_calculation_institution_type_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (index_market_classification_id_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (index_sequence_number_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (index_leverage_inverse_type_code_value, bytes) =>
                          match decode_bytes 80 bytes with
                          | None => None
                          | Some (index_name_value, bytes) =>
                              match decode_bytes 80 bytes with
                              | None => None
                              | Some (index_name_in_en_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (index_asset_classification_id_1_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (index_asset_classification_id_2_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (index_id_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (filler_4_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (end_keyword_value, bytes) =>
                                                      Some ({| message_sequence_number := message_sequence_number_value; index_calculation_institution_type_code := index_calculation_institution_type_code_value; index_market_classification_id := index_market_classification_id_value; index_sequence_number := index_sequence_number_value; index_leverage_inverse_type_code := index_leverage_inverse_type_code_value; index_name := index_name_value; index_name_in_en := index_name_in_en_value; index_asset_classification_id_1 := index_asset_classification_id_1_value; index_asset_classification_id_2 := index_asset_classification_id_2_value; index_id := index_id_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 204.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesEtpConstituentsMessage.

  Module SecuritiesKnockOutElwMessage.

    (** Knock-out ELW reference. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      base_price_to_knock_out_elw : list byte;
      knock_out_elw_rights : list byte;
      knock_out_elw_calculation_of_appraised_price : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (base_price_to_knock_out_elw record) = 13 /\
      Datatypes.length (knock_out_elw_rights record) = 200 /\
      Datatypes.length (knock_out_elw_calculation_of_appraised_price record) = 300 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 13 (base_price_to_knock_out_elw record) ++
      encode_bytes 200 (knock_out_elw_rights record) ++
      encode_bytes 300 (knock_out_elw_calculation_of_appraised_price record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (base_price_to_knock_out_elw_value, bytes) =>
                  match decode_bytes 200 bytes with
                  | None => None
                  | Some (knock_out_elw_rights_value, bytes) =>
                      match decode_bytes 300 bytes with
                      | None => None
                      | Some (knock_out_elw_calculation_of_appraised_price_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; base_price_to_knock_out_elw := base_price_to_knock_out_elw_value; knock_out_elw_rights := knock_out_elw_rights_value; knock_out_elw_calculation_of_appraised_price := knock_out_elw_calculation_of_appraised_price_value; end_keyword := end_keyword_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 534.
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

  End SecuritiesKnockOutElwMessage.

  Module SecuritiesKnockOutUnderlyingMessage.

    (** High/Low Price of Underlying Asset for Knock-out ELW. *)
    Record t := {
      isin_code : list byte;
      message_sequence_number : list byte;
      transmission_date : list byte;
      trading_date_of_underlying_asset : list byte;
      the_date_knock_out_occurred : list byte;
      ampm_type_code : list byte;
      underlying_i_s_i_n_code : list byte;
      index_id : list byte;
      todays_high : list byte;
      todays_low : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (transmission_date record) = 8 /\
      Datatypes.length (trading_date_of_underlying_asset record) = 8 /\
      Datatypes.length (the_date_knock_out_occurred record) = 8 /\
      Datatypes.length (ampm_type_code record) = 1 /\
      Datatypes.length (underlying_i_s_i_n_code record) = 12 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 8 (transmission_date record) ++
      encode_bytes 8 (trading_date_of_underlying_asset record) ++
      encode_bytes 8 (the_date_knock_out_occurred record) ++
      encode_bytes 1 (ampm_type_code record) ++
      encode_bytes 12 (underlying_i_s_i_n_code record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (message_sequence_number_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (transmission_date_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trading_date_of_underlying_asset_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (the_date_knock_out_occurred_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (ampm_type_code_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (underlying_i_s_i_n_code_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (index_id_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (todays_high_value, bytes) =>
                                          match decode_bytes 11 bytes with
                                          | None => None
                                          | Some (todays_low_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (filler_4_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (end_keyword_value, bytes) =>
                                                      Some ({| isin_code := isin_code_value; message_sequence_number := message_sequence_number_value; transmission_date := transmission_date_value; trading_date_of_underlying_asset := trading_date_of_underlying_asset_value; the_date_knock_out_occurred := the_date_knock_out_occurred_value; ampm_type_code := ampm_type_code_value; underlying_i_s_i_n_code := underlying_i_s_i_n_code_value; index_id := index_id_value; todays_high := todays_high_value; todays_low := todays_low_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 90.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesKnockOutUnderlyingMessage.

  Module SecuritiesProgramTradingActivityPerInvestorMessage.

    (** Program Trading Activity per Investor (IFMSSTD0008). Aggregated arbitrage / non-arbitrage bid/ask volumes and values per investor category. *)
    Record t := {
      calculation_time : list byte;
      investor_code : list byte;
      sell_side_arbitrage_volume : list byte;
      sell_side_arbitrage_value : list byte;
      sell_side_non_arbitrage_volume : list byte;
      sell_side_non_arbitrage_value : list byte;
      buy_side_arbitrage_volume : list byte;
      buy_side_arbitrage_value : list byte;
      buy_side_non_arbitrage_volume : list byte;
      buy_side_non_arbitrage_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (calculation_time record) = 6 /\
      Datatypes.length (investor_code record) = 4 /\
      Datatypes.length (sell_side_arbitrage_volume record) = 15 /\
      Datatypes.length (sell_side_arbitrage_value record) = 22 /\
      Datatypes.length (sell_side_non_arbitrage_volume record) = 15 /\
      Datatypes.length (sell_side_non_arbitrage_value record) = 22 /\
      Datatypes.length (buy_side_arbitrage_volume record) = 15 /\
      Datatypes.length (buy_side_arbitrage_value record) = 22 /\
      Datatypes.length (buy_side_non_arbitrage_volume record) = 15 /\
      Datatypes.length (buy_side_non_arbitrage_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (calculation_time record) ++
      encode_bytes 4 (investor_code record) ++
      encode_bytes 15 (sell_side_arbitrage_volume record) ++
      encode_bytes 22 (sell_side_arbitrage_value record) ++
      encode_bytes 15 (sell_side_non_arbitrage_volume record) ++
      encode_bytes 22 (sell_side_non_arbitrage_value record) ++
      encode_bytes 15 (buy_side_arbitrage_volume record) ++
      encode_bytes 22 (buy_side_arbitrage_value record) ++
      encode_bytes 15 (buy_side_non_arbitrage_volume record) ++
      encode_bytes 22 (buy_side_non_arbitrage_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (calculation_time_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (investor_code_value, bytes) =>
              match decode_bytes 15 bytes with
              | None => None
              | Some (sell_side_arbitrage_volume_value, bytes) =>
                  match decode_bytes 22 bytes with
                  | None => None
                  | Some (sell_side_arbitrage_value_value, bytes) =>
                      match decode_bytes 15 bytes with
                      | None => None
                      | Some (sell_side_non_arbitrage_volume_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (sell_side_non_arbitrage_value_value, bytes) =>
                              match decode_bytes 15 bytes with
                              | None => None
                              | Some (buy_side_arbitrage_volume_value, bytes) =>
                                  match decode_bytes 22 bytes with
                                  | None => None
                                  | Some (buy_side_arbitrage_value_value, bytes) =>
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (buy_side_non_arbitrage_volume_value, bytes) =>
                                          match decode_bytes 22 bytes with
                                          | None => None
                                          | Some (buy_side_non_arbitrage_value_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (end_keyword_value, bytes) =>
                                                  Some ({| calculation_time := calculation_time_value; investor_code := investor_code_value; sell_side_arbitrage_volume := sell_side_arbitrage_volume_value; sell_side_arbitrage_value := sell_side_arbitrage_value_value; sell_side_non_arbitrage_volume := sell_side_non_arbitrage_volume_value; sell_side_non_arbitrage_value := sell_side_non_arbitrage_value_value; buy_side_arbitrage_volume := buy_side_arbitrage_volume_value; buy_side_arbitrage_value := buy_side_arbitrage_value_value; buy_side_non_arbitrage_volume := buy_side_non_arbitrage_volume_value; buy_side_non_arbitrage_value := buy_side_non_arbitrage_value_value; end_keyword := end_keyword_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 159.
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

  End SecuritiesProgramTradingActivityPerInvestorMessage.

  Module SecuritiesProgramTradingInformationPerIssueAggregatedMessage.

    (** Program Trading Information per Issue Aggregated Information (IFMSSTD0009). Per-issue arbitrage / non-arbitrage remaining and traded quantities, plus ask/bid trust and principal trading volumes and values. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      sell_side_arbitrage_trading_remaining_quantity : list byte;
      buy_side_arbitrage_trading_remaining_quantity : list byte;
      sell_side_non_arbitrage_remaining_quantity : list byte;
      buy_side_non_arbitrage_remaining_quantity : list byte;
      sell_side_arbitrage_quantity : list byte;
      buy_side_arbitrage_quantity : list byte;
      sell_side_non_arbitrage_quantity : list byte;
      buy_side_non_arbitrage_quantity : list byte;
      arbitrage_ask_trust_trading_volume : list byte;
      arbitrage_ask_principal_trading_volume : list byte;
      arbitrage_bid_trust_trading_volume : list byte;
      arbitrage_bid_principal_trading_volume : list byte;
      non_arbitrage_ask_trust_trading_volume : list byte;
      non_arbitrage_ask_principal_trading_volume : list byte;
      non_arbitrage_bid_trust_trading_volume : list byte;
      non_arbitrage_bid_principal_trading_volume : list byte;
      arbitrage_ask_trust_trading_value : list byte;
      arbitrage_ask_principal_trading_value : list byte;
      arbitrage_bid_trust_trading_value : list byte;
      arbitrage_bid_principal_trading_value : list byte;
      non_arbitrage_ask_trust_trading_value : list byte;
      non_arbitrage_ask_principal_trading_value : list byte;
      non_arbitrage_bid_trust_trading_value : list byte;
      non_arbitrage_bid_principal_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (sell_side_arbitrage_trading_remaining_quantity record) = 15 /\
      Datatypes.length (buy_side_arbitrage_trading_remaining_quantity record) = 15 /\
      Datatypes.length (sell_side_non_arbitrage_remaining_quantity record) = 15 /\
      Datatypes.length (buy_side_non_arbitrage_remaining_quantity record) = 15 /\
      Datatypes.length (sell_side_arbitrage_quantity record) = 15 /\
      Datatypes.length (buy_side_arbitrage_quantity record) = 15 /\
      Datatypes.length (sell_side_non_arbitrage_quantity record) = 15 /\
      Datatypes.length (buy_side_non_arbitrage_quantity record) = 15 /\
      Datatypes.length (arbitrage_ask_trust_trading_volume record) = 10 /\
      Datatypes.length (arbitrage_ask_principal_trading_volume record) = 10 /\
      Datatypes.length (arbitrage_bid_trust_trading_volume record) = 10 /\
      Datatypes.length (arbitrage_bid_principal_trading_volume record) = 10 /\
      Datatypes.length (non_arbitrage_ask_trust_trading_volume record) = 10 /\
      Datatypes.length (non_arbitrage_ask_principal_trading_volume record) = 10 /\
      Datatypes.length (non_arbitrage_bid_trust_trading_volume record) = 10 /\
      Datatypes.length (non_arbitrage_bid_principal_trading_volume record) = 10 /\
      Datatypes.length (arbitrage_ask_trust_trading_value record) = 22 /\
      Datatypes.length (arbitrage_ask_principal_trading_value record) = 22 /\
      Datatypes.length (arbitrage_bid_trust_trading_value record) = 22 /\
      Datatypes.length (arbitrage_bid_principal_trading_value record) = 22 /\
      Datatypes.length (non_arbitrage_ask_trust_trading_value record) = 22 /\
      Datatypes.length (non_arbitrage_ask_principal_trading_value record) = 22 /\
      Datatypes.length (non_arbitrage_bid_trust_trading_value record) = 22 /\
      Datatypes.length (non_arbitrage_bid_principal_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 15 (sell_side_arbitrage_trading_remaining_quantity record) ++
      encode_bytes 15 (buy_side_arbitrage_trading_remaining_quantity record) ++
      encode_bytes 15 (sell_side_non_arbitrage_remaining_quantity record) ++
      encode_bytes 15 (buy_side_non_arbitrage_remaining_quantity record) ++
      encode_bytes 15 (sell_side_arbitrage_quantity record) ++
      encode_bytes 15 (buy_side_arbitrage_quantity record) ++
      encode_bytes 15 (sell_side_non_arbitrage_quantity record) ++
      encode_bytes 15 (buy_side_non_arbitrage_quantity record) ++
      encode_bytes 10 (arbitrage_ask_trust_trading_volume record) ++
      encode_bytes 10 (arbitrage_ask_principal_trading_volume record) ++
      encode_bytes 10 (arbitrage_bid_trust_trading_volume record) ++
      encode_bytes 10 (arbitrage_bid_principal_trading_volume record) ++
      encode_bytes 10 (non_arbitrage_ask_trust_trading_volume record) ++
      encode_bytes 10 (non_arbitrage_ask_principal_trading_volume record) ++
      encode_bytes 10 (non_arbitrage_bid_trust_trading_volume record) ++
      encode_bytes 10 (non_arbitrage_bid_principal_trading_volume record) ++
      encode_bytes 22 (arbitrage_ask_trust_trading_value record) ++
      encode_bytes 22 (arbitrage_ask_principal_trading_value record) ++
      encode_bytes 22 (arbitrage_bid_trust_trading_value record) ++
      encode_bytes 22 (arbitrage_bid_principal_trading_value record) ++
      encode_bytes 22 (non_arbitrage_ask_trust_trading_value record) ++
      encode_bytes 22 (non_arbitrage_ask_principal_trading_value record) ++
      encode_bytes 22 (non_arbitrage_bid_trust_trading_value record) ++
      encode_bytes 22 (non_arbitrage_bid_principal_trading_value record) ++
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
              | Some (sell_side_arbitrage_trading_remaining_quantity_value, bytes) =>
                  match decode_bytes 15 bytes with
                  | None => None
                  | Some (buy_side_arbitrage_trading_remaining_quantity_value, bytes) =>
                      match decode_bytes 15 bytes with
                      | None => None
                      | Some (sell_side_non_arbitrage_remaining_quantity_value, bytes) =>
                          match decode_bytes 15 bytes with
                          | None => None
                          | Some (buy_side_non_arbitrage_remaining_quantity_value, bytes) =>
                              match decode_bytes 15 bytes with
                              | None => None
                              | Some (sell_side_arbitrage_quantity_value, bytes) =>
                                  match decode_bytes 15 bytes with
                                  | None => None
                                  | Some (buy_side_arbitrage_quantity_value, bytes) =>
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (sell_side_non_arbitrage_quantity_value, bytes) =>
                                          match decode_bytes 15 bytes with
                                          | None => None
                                          | Some (buy_side_non_arbitrage_quantity_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (arbitrage_ask_trust_trading_volume_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (arbitrage_ask_principal_trading_volume_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (arbitrage_bid_trust_trading_volume_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (arbitrage_bid_principal_trading_volume_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (non_arbitrage_ask_trust_trading_volume_value, bytes) =>
                                                                  match decode_bytes 10 bytes with
                                                                  | None => None
                                                                  | Some (non_arbitrage_ask_principal_trading_volume_value, bytes) =>
                                                                      match decode_bytes 10 bytes with
                                                                      | None => None
                                                                      | Some (non_arbitrage_bid_trust_trading_volume_value, bytes) =>
                                                                          match decode_bytes 10 bytes with
                                                                          | None => None
                                                                          | Some (non_arbitrage_bid_principal_trading_volume_value, bytes) =>
                                                                              match decode_bytes 22 bytes with
                                                                              | None => None
                                                                              | Some (arbitrage_ask_trust_trading_value_value, bytes) =>
                                                                                  match decode_bytes 22 bytes with
                                                                                  | None => None
                                                                                  | Some (arbitrage_ask_principal_trading_value_value, bytes) =>
                                                                                      match decode_bytes 22 bytes with
                                                                                      | None => None
                                                                                      | Some (arbitrage_bid_trust_trading_value_value, bytes) =>
                                                                                          match decode_bytes 22 bytes with
                                                                                          | None => None
                                                                                          | Some (arbitrage_bid_principal_trading_value_value, bytes) =>
                                                                                              match decode_bytes 22 bytes with
                                                                                              | None => None
                                                                                              | Some (non_arbitrage_ask_trust_trading_value_value, bytes) =>
                                                                                                  match decode_bytes 22 bytes with
                                                                                                  | None => None
                                                                                                  | Some (non_arbitrage_ask_principal_trading_value_value, bytes) =>
                                                                                                      match decode_bytes 22 bytes with
                                                                                                      | None => None
                                                                                                      | Some (non_arbitrage_bid_trust_trading_value_value, bytes) =>
                                                                                                          match decode_bytes 22 bytes with
                                                                                                          | None => None
                                                                                                          | Some (non_arbitrage_bid_principal_trading_value_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                  Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; sell_side_arbitrage_trading_remaining_quantity := sell_side_arbitrage_trading_remaining_quantity_value; buy_side_arbitrage_trading_remaining_quantity := buy_side_arbitrage_trading_remaining_quantity_value; sell_side_non_arbitrage_remaining_quantity := sell_side_non_arbitrage_remaining_quantity_value; buy_side_non_arbitrage_remaining_quantity := buy_side_non_arbitrage_remaining_quantity_value; sell_side_arbitrage_quantity := sell_side_arbitrage_quantity_value; buy_side_arbitrage_quantity := buy_side_arbitrage_quantity_value; sell_side_non_arbitrage_quantity := sell_side_non_arbitrage_quantity_value; buy_side_non_arbitrage_quantity := buy_side_non_arbitrage_quantity_value; arbitrage_ask_trust_trading_volume := arbitrage_ask_trust_trading_volume_value; arbitrage_ask_principal_trading_volume := arbitrage_ask_principal_trading_volume_value; arbitrage_bid_trust_trading_volume := arbitrage_bid_trust_trading_volume_value; arbitrage_bid_principal_trading_volume := arbitrage_bid_principal_trading_volume_value; non_arbitrage_ask_trust_trading_volume := non_arbitrage_ask_trust_trading_volume_value; non_arbitrage_ask_principal_trading_volume := non_arbitrage_ask_principal_trading_volume_value; non_arbitrage_bid_trust_trading_volume := non_arbitrage_bid_trust_trading_volume_value; non_arbitrage_bid_principal_trading_volume := non_arbitrage_bid_principal_trading_volume_value; arbitrage_ask_trust_trading_value := arbitrage_ask_trust_trading_value_value; arbitrage_ask_principal_trading_value := arbitrage_ask_principal_trading_value_value; arbitrage_bid_trust_trading_value := arbitrage_bid_trust_trading_value_value; arbitrage_bid_principal_trading_value := arbitrage_bid_principal_trading_value_value; non_arbitrage_ask_trust_trading_value := non_arbitrage_ask_trust_trading_value_value; non_arbitrage_ask_principal_trading_value := non_arbitrage_ask_principal_trading_value_value; non_arbitrage_bid_trust_trading_value := non_arbitrage_bid_trust_trading_value_value; non_arbitrage_bid_principal_trading_value := non_arbitrage_bid_principal_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

  End SecuritiesProgramTradingInformationPerIssueAggregatedMessage.

  Module SecuritiesProgramTradingInformationOfTotalAggregatedMessage.

    (** Program Trading Information of Total Aggregated Information (IFMSSTD0010). Market-wide arbitrage / non-arbitrage remaining and traded quantities, plus ask/bid trust and principal trading volumes and values. *)
    Record t := {
      sell_side_arbitrage_trading_remaining_quantity : list byte;
      buy_side_arbitrage_trading_remaining_quantity : list byte;
      sell_side_non_arbitrage_remaining_quantity : list byte;
      buy_side_non_arbitrage_remaining_quantity : list byte;
      sell_side_arbitrage_quantity : list byte;
      buy_side_arbitrage_quantity : list byte;
      sell_side_non_arbitrage_quantity : list byte;
      buy_side_non_arbitrage_quantity : list byte;
      arbitrage_ask_trust_trading_volume : list byte;
      arbitrage_ask_principal_trading_volume : list byte;
      arbitrage_bid_trust_trading_volume : list byte;
      arbitrage_bid_principal_trading_volume : list byte;
      non_arbitrage_ask_trust_trading_volume : list byte;
      non_arbitrage_ask_principal_trading_volume : list byte;
      non_arbitrage_bid_trust_trading_volume : list byte;
      non_arbitrage_bid_principal_trading_volume : list byte;
      arbitrage_ask_trust_trading_value : list byte;
      arbitrage_ask_principal_trading_value : list byte;
      arbitrage_bid_trust_trading_value : list byte;
      arbitrage_bid_principal_trading_value : list byte;
      non_arbitrage_ask_trust_trading_value : list byte;
      non_arbitrage_ask_principal_trading_value : list byte;
      non_arbitrage_bid_trust_trading_value : list byte;
      non_arbitrage_bid_principal_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sell_side_arbitrage_trading_remaining_quantity record) = 15 /\
      Datatypes.length (buy_side_arbitrage_trading_remaining_quantity record) = 15 /\
      Datatypes.length (sell_side_non_arbitrage_remaining_quantity record) = 15 /\
      Datatypes.length (buy_side_non_arbitrage_remaining_quantity record) = 15 /\
      Datatypes.length (sell_side_arbitrage_quantity record) = 15 /\
      Datatypes.length (buy_side_arbitrage_quantity record) = 15 /\
      Datatypes.length (sell_side_non_arbitrage_quantity record) = 15 /\
      Datatypes.length (buy_side_non_arbitrage_quantity record) = 15 /\
      Datatypes.length (arbitrage_ask_trust_trading_volume record) = 10 /\
      Datatypes.length (arbitrage_ask_principal_trading_volume record) = 10 /\
      Datatypes.length (arbitrage_bid_trust_trading_volume record) = 10 /\
      Datatypes.length (arbitrage_bid_principal_trading_volume record) = 10 /\
      Datatypes.length (non_arbitrage_ask_trust_trading_volume record) = 10 /\
      Datatypes.length (non_arbitrage_ask_principal_trading_volume record) = 10 /\
      Datatypes.length (non_arbitrage_bid_trust_trading_volume record) = 10 /\
      Datatypes.length (non_arbitrage_bid_principal_trading_volume record) = 10 /\
      Datatypes.length (arbitrage_ask_trust_trading_value record) = 22 /\
      Datatypes.length (arbitrage_ask_principal_trading_value record) = 22 /\
      Datatypes.length (arbitrage_bid_trust_trading_value record) = 22 /\
      Datatypes.length (arbitrage_bid_principal_trading_value record) = 22 /\
      Datatypes.length (non_arbitrage_ask_trust_trading_value record) = 22 /\
      Datatypes.length (non_arbitrage_ask_principal_trading_value record) = 22 /\
      Datatypes.length (non_arbitrage_bid_trust_trading_value record) = 22 /\
      Datatypes.length (non_arbitrage_bid_principal_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (sell_side_arbitrage_trading_remaining_quantity record) ++
      encode_bytes 15 (buy_side_arbitrage_trading_remaining_quantity record) ++
      encode_bytes 15 (sell_side_non_arbitrage_remaining_quantity record) ++
      encode_bytes 15 (buy_side_non_arbitrage_remaining_quantity record) ++
      encode_bytes 15 (sell_side_arbitrage_quantity record) ++
      encode_bytes 15 (buy_side_arbitrage_quantity record) ++
      encode_bytes 15 (sell_side_non_arbitrage_quantity record) ++
      encode_bytes 15 (buy_side_non_arbitrage_quantity record) ++
      encode_bytes 10 (arbitrage_ask_trust_trading_volume record) ++
      encode_bytes 10 (arbitrage_ask_principal_trading_volume record) ++
      encode_bytes 10 (arbitrage_bid_trust_trading_volume record) ++
      encode_bytes 10 (arbitrage_bid_principal_trading_volume record) ++
      encode_bytes 10 (non_arbitrage_ask_trust_trading_volume record) ++
      encode_bytes 10 (non_arbitrage_ask_principal_trading_volume record) ++
      encode_bytes 10 (non_arbitrage_bid_trust_trading_volume record) ++
      encode_bytes 10 (non_arbitrage_bid_principal_trading_volume record) ++
      encode_bytes 22 (arbitrage_ask_trust_trading_value record) ++
      encode_bytes 22 (arbitrage_ask_principal_trading_value record) ++
      encode_bytes 22 (arbitrage_bid_trust_trading_value record) ++
      encode_bytes 22 (arbitrage_bid_principal_trading_value record) ++
      encode_bytes 22 (non_arbitrage_ask_trust_trading_value record) ++
      encode_bytes 22 (non_arbitrage_ask_principal_trading_value record) ++
      encode_bytes 22 (non_arbitrage_bid_trust_trading_value record) ++
      encode_bytes 22 (non_arbitrage_bid_principal_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (sell_side_arbitrage_trading_remaining_quantity_value, bytes) =>
          match decode_bytes 15 bytes with
          | None => None
          | Some (buy_side_arbitrage_trading_remaining_quantity_value, bytes) =>
              match decode_bytes 15 bytes with
              | None => None
              | Some (sell_side_non_arbitrage_remaining_quantity_value, bytes) =>
                  match decode_bytes 15 bytes with
                  | None => None
                  | Some (buy_side_non_arbitrage_remaining_quantity_value, bytes) =>
                      match decode_bytes 15 bytes with
                      | None => None
                      | Some (sell_side_arbitrage_quantity_value, bytes) =>
                          match decode_bytes 15 bytes with
                          | None => None
                          | Some (buy_side_arbitrage_quantity_value, bytes) =>
                              match decode_bytes 15 bytes with
                              | None => None
                              | Some (sell_side_non_arbitrage_quantity_value, bytes) =>
                                  match decode_bytes 15 bytes with
                                  | None => None
                                  | Some (buy_side_non_arbitrage_quantity_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (arbitrage_ask_trust_trading_volume_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (arbitrage_ask_principal_trading_volume_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (arbitrage_bid_trust_trading_volume_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (arbitrage_bid_principal_trading_volume_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (non_arbitrage_ask_trust_trading_volume_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (non_arbitrage_ask_principal_trading_volume_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (non_arbitrage_bid_trust_trading_volume_value, bytes) =>
                                                                  match decode_bytes 10 bytes with
                                                                  | None => None
                                                                  | Some (non_arbitrage_bid_principal_trading_volume_value, bytes) =>
                                                                      match decode_bytes 22 bytes with
                                                                      | None => None
                                                                      | Some (arbitrage_ask_trust_trading_value_value, bytes) =>
                                                                          match decode_bytes 22 bytes with
                                                                          | None => None
                                                                          | Some (arbitrage_ask_principal_trading_value_value, bytes) =>
                                                                              match decode_bytes 22 bytes with
                                                                              | None => None
                                                                              | Some (arbitrage_bid_trust_trading_value_value, bytes) =>
                                                                                  match decode_bytes 22 bytes with
                                                                                  | None => None
                                                                                  | Some (arbitrage_bid_principal_trading_value_value, bytes) =>
                                                                                      match decode_bytes 22 bytes with
                                                                                      | None => None
                                                                                      | Some (non_arbitrage_ask_trust_trading_value_value, bytes) =>
                                                                                          match decode_bytes 22 bytes with
                                                                                          | None => None
                                                                                          | Some (non_arbitrage_ask_principal_trading_value_value, bytes) =>
                                                                                              match decode_bytes 22 bytes with
                                                                                              | None => None
                                                                                              | Some (non_arbitrage_bid_trust_trading_value_value, bytes) =>
                                                                                                  match decode_bytes 22 bytes with
                                                                                                  | None => None
                                                                                                  | Some (non_arbitrage_bid_principal_trading_value_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                          Some ({| sell_side_arbitrage_trading_remaining_quantity := sell_side_arbitrage_trading_remaining_quantity_value; buy_side_arbitrage_trading_remaining_quantity := buy_side_arbitrage_trading_remaining_quantity_value; sell_side_non_arbitrage_remaining_quantity := sell_side_non_arbitrage_remaining_quantity_value; buy_side_non_arbitrage_remaining_quantity := buy_side_non_arbitrage_remaining_quantity_value; sell_side_arbitrage_quantity := sell_side_arbitrage_quantity_value; buy_side_arbitrage_quantity := buy_side_arbitrage_quantity_value; sell_side_non_arbitrage_quantity := sell_side_non_arbitrage_quantity_value; buy_side_non_arbitrage_quantity := buy_side_non_arbitrage_quantity_value; arbitrage_ask_trust_trading_volume := arbitrage_ask_trust_trading_volume_value; arbitrage_ask_principal_trading_volume := arbitrage_ask_principal_trading_volume_value; arbitrage_bid_trust_trading_volume := arbitrage_bid_trust_trading_volume_value; arbitrage_bid_principal_trading_volume := arbitrage_bid_principal_trading_volume_value; non_arbitrage_ask_trust_trading_volume := non_arbitrage_ask_trust_trading_volume_value; non_arbitrage_ask_principal_trading_volume := non_arbitrage_ask_principal_trading_volume_value; non_arbitrage_bid_trust_trading_volume := non_arbitrage_bid_trust_trading_volume_value; non_arbitrage_bid_principal_trading_volume := non_arbitrage_bid_principal_trading_volume_value; arbitrage_ask_trust_trading_value := arbitrage_ask_trust_trading_value_value; arbitrage_ask_principal_trading_value := arbitrage_ask_principal_trading_value_value; arbitrage_bid_trust_trading_value := arbitrage_bid_trust_trading_value_value; arbitrage_bid_principal_trading_value := arbitrage_bid_principal_trading_value_value; non_arbitrage_ask_trust_trading_value := non_arbitrage_ask_trust_trading_value_value; non_arbitrage_ask_principal_trading_value := non_arbitrage_ask_principal_trading_value_value; non_arbitrage_bid_trust_trading_value := non_arbitrage_bid_trust_trading_value_value; non_arbitrage_bid_principal_trading_value := non_arbitrage_bid_principal_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 377.
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
      rewrite decode_encode_uint by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesProgramTradingInformationOfTotalAggregatedMessage.

  Module SecuritiesTopFiveTradersActivitiesMessage.

    (** Top Five Traders' Activities for KOSPI (Securities A). Top Five Traders' Activities (IFMSSTD0006). Ask/bid member number, traded volume and value for the top five member firms per issue. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      member_number_1_for_ask : list byte;
      ask_trading_volume_1 : list byte;
      ask_trading_value_1 : list byte;
      member_number_1_for_bid : list byte;
      bid_trading_volume_1 : list byte;
      bid_trading_value_1 : list byte;
      member_number_2_for_ask : list byte;
      ask_trading_volume_2 : list byte;
      ask_trading_value_2 : list byte;
      member_number_2_for_bid : list byte;
      bid_trading_volume_2 : list byte;
      bid_trading_value_2 : list byte;
      member_number_3_for_ask : list byte;
      ask_trading_volume_3 : list byte;
      ask_trading_value_3 : list byte;
      member_number_3_for_bid : list byte;
      bid_trading_volume_3 : list byte;
      bid_trading_value_3 : list byte;
      member_number_4_for_ask : list byte;
      ask_trading_volume_4 : list byte;
      ask_trading_value_4 : list byte;
      member_number_4_for_bid : list byte;
      bid_trading_volume_4 : list byte;
      bid_trading_value_4 : list byte;
      member_number_5_for_ask : list byte;
      ask_trading_volume_5 : list byte;
      ask_trading_value_5 : list byte;
      member_number_5_for_bid : list byte;
      bid_trading_volume_5 : list byte;
      bid_trading_value_5 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (member_number_1_for_ask record) = 5 /\
      Datatypes.length (ask_trading_volume_1 record) = 12 /\
      Datatypes.length (ask_trading_value_1 record) = 22 /\
      Datatypes.length (member_number_1_for_bid record) = 5 /\
      Datatypes.length (bid_trading_volume_1 record) = 12 /\
      Datatypes.length (bid_trading_value_1 record) = 22 /\
      Datatypes.length (member_number_2_for_ask record) = 5 /\
      Datatypes.length (ask_trading_volume_2 record) = 12 /\
      Datatypes.length (ask_trading_value_2 record) = 22 /\
      Datatypes.length (member_number_2_for_bid record) = 5 /\
      Datatypes.length (bid_trading_volume_2 record) = 12 /\
      Datatypes.length (bid_trading_value_2 record) = 22 /\
      Datatypes.length (member_number_3_for_ask record) = 5 /\
      Datatypes.length (ask_trading_volume_3 record) = 12 /\
      Datatypes.length (ask_trading_value_3 record) = 22 /\
      Datatypes.length (member_number_3_for_bid record) = 5 /\
      Datatypes.length (bid_trading_volume_3 record) = 12 /\
      Datatypes.length (bid_trading_value_3 record) = 22 /\
      Datatypes.length (member_number_4_for_ask record) = 5 /\
      Datatypes.length (ask_trading_volume_4 record) = 12 /\
      Datatypes.length (ask_trading_value_4 record) = 22 /\
      Datatypes.length (member_number_4_for_bid record) = 5 /\
      Datatypes.length (bid_trading_volume_4 record) = 12 /\
      Datatypes.length (bid_trading_value_4 record) = 22 /\
      Datatypes.length (member_number_5_for_ask record) = 5 /\
      Datatypes.length (ask_trading_volume_5 record) = 12 /\
      Datatypes.length (ask_trading_value_5 record) = 22 /\
      Datatypes.length (member_number_5_for_bid record) = 5 /\
      Datatypes.length (bid_trading_volume_5 record) = 12 /\
      Datatypes.length (bid_trading_value_5 record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 5 (member_number_1_for_ask record) ++
      encode_bytes 12 (ask_trading_volume_1 record) ++
      encode_bytes 22 (ask_trading_value_1 record) ++
      encode_bytes 5 (member_number_1_for_bid record) ++
      encode_bytes 12 (bid_trading_volume_1 record) ++
      encode_bytes 22 (bid_trading_value_1 record) ++
      encode_bytes 5 (member_number_2_for_ask record) ++
      encode_bytes 12 (ask_trading_volume_2 record) ++
      encode_bytes 22 (ask_trading_value_2 record) ++
      encode_bytes 5 (member_number_2_for_bid record) ++
      encode_bytes 12 (bid_trading_volume_2 record) ++
      encode_bytes 22 (bid_trading_value_2 record) ++
      encode_bytes 5 (member_number_3_for_ask record) ++
      encode_bytes 12 (ask_trading_volume_3 record) ++
      encode_bytes 22 (ask_trading_value_3 record) ++
      encode_bytes 5 (member_number_3_for_bid record) ++
      encode_bytes 12 (bid_trading_volume_3 record) ++
      encode_bytes 22 (bid_trading_value_3 record) ++
      encode_bytes 5 (member_number_4_for_ask record) ++
      encode_bytes 12 (ask_trading_volume_4 record) ++
      encode_bytes 22 (ask_trading_value_4 record) ++
      encode_bytes 5 (member_number_4_for_bid record) ++
      encode_bytes 12 (bid_trading_volume_4 record) ++
      encode_bytes 22 (bid_trading_value_4 record) ++
      encode_bytes 5 (member_number_5_for_ask record) ++
      encode_bytes 12 (ask_trading_volume_5 record) ++
      encode_bytes 22 (ask_trading_value_5 record) ++
      encode_bytes 5 (member_number_5_for_bid record) ++
      encode_bytes 12 (bid_trading_volume_5 record) ++
      encode_bytes 22 (bid_trading_value_5 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (member_number_1_for_ask_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (ask_trading_volume_1_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (ask_trading_value_1_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (member_number_1_for_bid_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (bid_trading_volume_1_value, bytes) =>
                                  match decode_bytes 22 bytes with
                                  | None => None
                                  | Some (bid_trading_value_1_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (member_number_2_for_ask_value, bytes) =>
                                          match decode_bytes 12 bytes with
                                          | None => None
                                          | Some (ask_trading_volume_2_value, bytes) =>
                                              match decode_bytes 22 bytes with
                                              | None => None
                                              | Some (ask_trading_value_2_value, bytes) =>
                                                  match decode_bytes 5 bytes with
                                                  | None => None
                                                  | Some (member_number_2_for_bid_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (bid_trading_volume_2_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (bid_trading_value_2_value, bytes) =>
                                                              match decode_bytes 5 bytes with
                                                              | None => None
                                                              | Some (member_number_3_for_ask_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (ask_trading_volume_3_value, bytes) =>
                                                                      match decode_bytes 22 bytes with
                                                                      | None => None
                                                                      | Some (ask_trading_value_3_value, bytes) =>
                                                                          match decode_bytes 5 bytes with
                                                                          | None => None
                                                                          | Some (member_number_3_for_bid_value, bytes) =>
                                                                              match decode_bytes 12 bytes with
                                                                              | None => None
                                                                              | Some (bid_trading_volume_3_value, bytes) =>
                                                                                  match decode_bytes 22 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_trading_value_3_value, bytes) =>
                                                                                      match decode_bytes 5 bytes with
                                                                                      | None => None
                                                                                      | Some (member_number_4_for_ask_value, bytes) =>
                                                                                          match decode_bytes 12 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_trading_volume_4_value, bytes) =>
                                                                                              match decode_bytes 22 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_trading_value_4_value, bytes) =>
                                                                                                  match decode_bytes 5 bytes with
                                                                                                  | None => None
                                                                                                  | Some (member_number_4_for_bid_value, bytes) =>
                                                                                                      match decode_bytes 12 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_trading_volume_4_value, bytes) =>
                                                                                                          match decode_bytes 22 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_trading_value_4_value, bytes) =>
                                                                                                              match decode_bytes 5 bytes with
                                                                                                              | None => None
                                                                                                              | Some (member_number_5_for_ask_value, bytes) =>
                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_trading_volume_5_value, bytes) =>
                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_trading_value_5_value, bytes) =>
                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (member_number_5_for_bid_value, bytes) =>
                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_trading_volume_5_value, bytes) =>
                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_trading_value_5_value, bytes) =>
                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                                                          Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; member_number_1_for_ask := member_number_1_for_ask_value; ask_trading_volume_1 := ask_trading_volume_1_value; ask_trading_value_1 := ask_trading_value_1_value; member_number_1_for_bid := member_number_1_for_bid_value; bid_trading_volume_1 := bid_trading_volume_1_value; bid_trading_value_1 := bid_trading_value_1_value; member_number_2_for_ask := member_number_2_for_ask_value; ask_trading_volume_2 := ask_trading_volume_2_value; ask_trading_value_2 := ask_trading_value_2_value; member_number_2_for_bid := member_number_2_for_bid_value; bid_trading_volume_2 := bid_trading_volume_2_value; bid_trading_value_2 := bid_trading_value_2_value; member_number_3_for_ask := member_number_3_for_ask_value; ask_trading_volume_3 := ask_trading_volume_3_value; ask_trading_value_3 := ask_trading_value_3_value; member_number_3_for_bid := member_number_3_for_bid_value; bid_trading_volume_3 := bid_trading_volume_3_value; bid_trading_value_3 := bid_trading_value_3_value; member_number_4_for_ask := member_number_4_for_ask_value; ask_trading_volume_4 := ask_trading_volume_4_value; ask_trading_value_4 := ask_trading_value_4_value; member_number_4_for_bid := member_number_4_for_bid_value; bid_trading_volume_4 := bid_trading_volume_4_value; bid_trading_value_4 := bid_trading_value_4_value; member_number_5_for_ask := member_number_5_for_ask_value; ask_trading_volume_5 := ask_trading_volume_5_value; ask_trading_value_5 := ask_trading_value_5_value; member_number_5_for_bid := member_number_5_for_bid_value; bid_trading_volume_5 := bid_trading_volume_5_value; bid_trading_value_5 := bid_trading_value_5_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 bound_32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesTopFiveTradersActivitiesMessage.

  Module SecuritiesCurrentMovementMessage.

    (** Current Movement (IFMSSTD0007) — Securities A KOSPI variant. Aggregate counts of issues by movement/trading state. *)
    Record t := {
      total_number_of_issues : list byte;
      number_of_issues_for_movement_calculation : list byte;
      number_of_issues_of_upper_limit : list byte;
      number_of_issues_of_going_up : list byte;
      number_of_issues_of_steadiness : list byte;
      number_of_issues_of_lower_limit : list byte;
      number_of_issues_of_going_down : list byte;
      number_of_issues_having_quotes : list byte;
      number_of_issues_of_which_quotes_are_increasing : list byte;
      number_of_issues_of_which_quotes_are_decreasing : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (total_number_of_issues record) = 5 /\
      Datatypes.length (number_of_issues_for_movement_calculation record) = 5 /\
      Datatypes.length (number_of_issues_of_upper_limit record) = 5 /\
      Datatypes.length (number_of_issues_of_going_up record) = 5 /\
      Datatypes.length (number_of_issues_of_steadiness record) = 5 /\
      Datatypes.length (number_of_issues_of_lower_limit record) = 5 /\
      Datatypes.length (number_of_issues_of_going_down record) = 5 /\
      Datatypes.length (number_of_issues_having_quotes record) = 5 /\
      Datatypes.length (number_of_issues_of_which_quotes_are_increasing record) = 5 /\
      Datatypes.length (number_of_issues_of_which_quotes_are_decreasing record) = 5 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (total_number_of_issues record) ++
      encode_bytes 5 (number_of_issues_for_movement_calculation record) ++
      encode_bytes 5 (number_of_issues_of_upper_limit record) ++
      encode_bytes 5 (number_of_issues_of_going_up record) ++
      encode_bytes 5 (number_of_issues_of_steadiness record) ++
      encode_bytes 5 (number_of_issues_of_lower_limit record) ++
      encode_bytes 5 (number_of_issues_of_going_down record) ++
      encode_bytes 5 (number_of_issues_having_quotes record) ++
      encode_bytes 5 (number_of_issues_of_which_quotes_are_increasing record) ++
      encode_bytes 5 (number_of_issues_of_which_quotes_are_decreasing record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (total_number_of_issues_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (number_of_issues_for_movement_calculation_value, bytes) =>
              match decode_bytes 5 bytes with
              | None => None
              | Some (number_of_issues_of_upper_limit_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (number_of_issues_of_going_up_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (number_of_issues_of_steadiness_value, bytes) =>
                          match decode_bytes 5 bytes with
                          | None => None
                          | Some (number_of_issues_of_lower_limit_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (number_of_issues_of_going_down_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (number_of_issues_having_quotes_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (number_of_issues_of_which_quotes_are_increasing_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (number_of_issues_of_which_quotes_are_decreasing_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (end_keyword_value, bytes) =>
                                                  Some ({| total_number_of_issues := total_number_of_issues_value; number_of_issues_for_movement_calculation := number_of_issues_for_movement_calculation_value; number_of_issues_of_upper_limit := number_of_issues_of_upper_limit_value; number_of_issues_of_going_up := number_of_issues_of_going_up_value; number_of_issues_of_steadiness := number_of_issues_of_steadiness_value; number_of_issues_of_lower_limit := number_of_issues_of_lower_limit_value; number_of_issues_of_going_down := number_of_issues_of_going_down_value; number_of_issues_having_quotes := number_of_issues_having_quotes_value; number_of_issues_of_which_quotes_are_increasing := number_of_issues_of_which_quotes_are_increasing_value; number_of_issues_of_which_quotes_are_decreasing := number_of_issues_of_which_quotes_are_decreasing_value; end_keyword := end_keyword_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
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

  End SecuritiesCurrentMovementMessage.

  Module SecuritiesClosingPriceTradeRemainingQuantityOnQuotesMessage.

    (** Equities Closing Price Trade — Remaining Quantity on Quotes (IFMSRPD0063) — Securities A KOSPI variant. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      accumulated_trading_volume : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (ask_total_volume record) = 12 /\
      Datatypes.length (bid_total_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 12 (ask_total_volume record) ++
      encode_bytes 12 (bid_total_volume record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (accumulated_trading_volume_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (ask_total_volume_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (bid_total_volume_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (end_keyword_value, bytes) =>
                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; accumulated_trading_volume := accumulated_trading_volume_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; end_keyword := end_keyword_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 77.
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

  End SecuritiesClosingPriceTradeRemainingQuantityOnQuotesMessage.

  Module SecuritiesABloxTradeQuotesMessage.

    (** A-Blox trade Quotes (IFMSRPD0066) — Securities A KOSPI variant. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      ask_bid_type_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (ask_bid_type_code record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 1 (ask_bid_type_code record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (ask_bid_type_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_bid_type_code := ask_bid_type_code_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
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

  End SecuritiesABloxTradeQuotesMessage.

  Module SecuritiesOneSidedAuctionMessage.

    (** One-Sided Auction (IFMSBTD0015) — Securities B KONEX. Auction application quantity, minimum trading volume/price. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      ask_bid_type_code : list byte;
      member_number : list byte;
      one_sided_auction_application_quantity : list byte;
      one_sided_auction_minimum_trading_volume : list byte;
      one_sided_auction_minimum_bidding_price : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (ask_bid_type_code record) = 1 /\
      Datatypes.length (member_number record) = 5 /\
      Datatypes.length (one_sided_auction_application_quantity record) = 12 /\
      Datatypes.length (one_sided_auction_minimum_trading_volume record) = 12 /\
      Datatypes.length (one_sided_auction_minimum_bidding_price record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 1 (ask_bid_type_code record) ++
      encode_bytes 5 (member_number record) ++
      encode_bytes 12 (one_sided_auction_application_quantity record) ++
      encode_bytes 12 (one_sided_auction_minimum_trading_volume record) ++
      encode_bytes 11 (one_sided_auction_minimum_bidding_price record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (ask_bid_type_code_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (member_number_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (one_sided_auction_application_quantity_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (one_sided_auction_minimum_trading_volume_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (one_sided_auction_minimum_bidding_price_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; ask_bid_type_code := ask_bid_type_code_value; member_number := member_number_value; one_sided_auction_application_quantity := one_sided_auction_application_quantity_value; one_sided_auction_minimum_trading_volume := one_sided_auction_minimum_trading_volume_value; one_sided_auction_minimum_bidding_price := one_sided_auction_minimum_bidding_price_value; end_keyword := end_keyword_value |}, bytes)
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

  End SecuritiesOneSidedAuctionMessage.

  Module SecuritiesSnapshotMmLpExcludedKonexMessage.

    (** Equities Snapshot (MM/LP Quotes Excluded) (IFMSRPD0021) — Securities B KONEX. 10-level depth of book snapshot excluding market-maker/liquidity-provider quotes. *)
    Record t := {
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      price_change_against_previous_day : list byte;
      a_price_change_against_the_previous_day : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      current_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
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
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      estimated_trading_price : list byte;
      estimated_trading_volume : list byte;
      closing_price_type_code : list byte;
      trading_halt : list byte;
      midpoint : list byte;
      ask_mid_price_total_volume : list byte;
      bid_mid_price_total_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (price_change_against_previous_day record) = 1 /\
      Datatypes.length (a_price_change_against_the_previous_day record) = 11 /\
      Datatypes.length (upper_limit_price record) = 11 /\
      Datatypes.length (lower_limit_price record) = 11 /\
      Datatypes.length (current_price record) = 11 /\
      Datatypes.length (opening_price record) = 11 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
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
      Datatypes.length (ask_level_6_price record) = 11 /\
      Datatypes.length (bid_level_6_price record) = 11 /\
      Datatypes.length (ask_level_6_volume record) = 12 /\
      Datatypes.length (bid_level_6_volume record) = 12 /\
      Datatypes.length (ask_level_7_price record) = 11 /\
      Datatypes.length (bid_level_7_price record) = 11 /\
      Datatypes.length (ask_level_7_volume record) = 12 /\
      Datatypes.length (bid_level_7_volume record) = 12 /\
      Datatypes.length (ask_level_8_price record) = 11 /\
      Datatypes.length (bid_level_8_price record) = 11 /\
      Datatypes.length (ask_level_8_volume record) = 12 /\
      Datatypes.length (bid_level_8_volume record) = 12 /\
      Datatypes.length (ask_level_9_price record) = 11 /\
      Datatypes.length (bid_level_9_price record) = 11 /\
      Datatypes.length (ask_level_9_volume record) = 12 /\
      Datatypes.length (bid_level_9_volume record) = 12 /\
      Datatypes.length (ask_level_10_price record) = 11 /\
      Datatypes.length (bid_level_10_price record) = 11 /\
      Datatypes.length (ask_level_10_volume record) = 12 /\
      Datatypes.length (bid_level_10_volume record) = 12 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (estimated_trading_price record) = 11 /\
      Datatypes.length (estimated_trading_volume record) = 12 /\
      Datatypes.length (closing_price_type_code record) = 1 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (midpoint record) = 11 /\
      Datatypes.length (ask_mid_price_total_volume record) = 12 /\
      Datatypes.length (bid_mid_price_total_volume record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 1 (price_change_against_previous_day record) ++
      encode_bytes 11 (a_price_change_against_the_previous_day record) ++
      encode_bytes 11 (upper_limit_price record) ++
      encode_bytes 11 (lower_limit_price record) ++
      encode_bytes 11 (current_price record) ++
      encode_bytes 11 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
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
      encode_bytes 11 (ask_level_6_price record) ++
      encode_bytes 11 (bid_level_6_price record) ++
      encode_bytes 12 (ask_level_6_volume record) ++
      encode_bytes 12 (bid_level_6_volume record) ++
      encode_bytes 11 (ask_level_7_price record) ++
      encode_bytes 11 (bid_level_7_price record) ++
      encode_bytes 12 (ask_level_7_volume record) ++
      encode_bytes 12 (bid_level_7_volume record) ++
      encode_bytes 11 (ask_level_8_price record) ++
      encode_bytes 11 (bid_level_8_price record) ++
      encode_bytes 12 (ask_level_8_volume record) ++
      encode_bytes 12 (bid_level_8_volume record) ++
      encode_bytes 11 (ask_level_9_price record) ++
      encode_bytes 11 (bid_level_9_price record) ++
      encode_bytes 12 (ask_level_9_volume record) ++
      encode_bytes 12 (bid_level_9_volume record) ++
      encode_bytes 11 (ask_level_10_price record) ++
      encode_bytes 11 (bid_level_10_price record) ++
      encode_bytes 12 (ask_level_10_volume record) ++
      encode_bytes 12 (bid_level_10_volume record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 11 (estimated_trading_price record) ++
      encode_bytes 12 (estimated_trading_volume record) ++
      encode_bytes 1 (closing_price_type_code record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 11 (midpoint record) ++
      encode_bytes 12 (ask_mid_price_total_volume record) ++
      encode_bytes 12 (bid_mid_price_total_volume record) ++
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
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (price_change_against_previous_day_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (a_price_change_against_the_previous_day_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (upper_limit_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (lower_limit_price_value, bytes) =>
                                      match decode_bytes 11 bytes with
                                      | None => None
                                      | Some (current_price_value, bytes) =>
                                          match decode_bytes 11 bytes with
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
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (closing_price_type_code_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (trading_halt_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (midpoint_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (ask_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (bid_mid_price_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                          Some ({| board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; price_change_against_previous_day := price_change_against_previous_day_value; a_price_change_against_the_previous_day := a_price_change_against_the_previous_day_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; current_price := current_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; closing_price_type_code := closing_price_type_code_value; trading_halt := trading_halt_value; midpoint := midpoint_value; ask_mid_price_total_volume := ask_mid_price_total_volume_value; bid_mid_price_total_volume := bid_mid_price_total_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 680.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 bound_64]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_64.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesSnapshotMmLpExcludedKonexMessage.

  Module BondsBatchDataMessage.

    (** Bonds Batch Data. Per-issue reference data dumped at start-of-day for General Bonds, KTB, and Baby Bonds. *)
    Record t := {
      message_sequence_number : list byte;
      total_number_of_instruments_of_the_contract : list byte;
      business_date : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      retail_bond_type_code : list byte;
      abbreviated_issue_name : list byte;
      abbreviated_issue_name_in_en : list byte;
      market_operation_product_id : list byte;
      bond_listing_type_code : list byte;
      bond_category_code : list byte;
      bond_guaranteed_type_code : list byte;
      coupon_payment_type_code : list byte;
      listing_date : list byte;
      issue_date : list byte;
      redemption_date : list byte;
      sale_date : list byte;
      bond_issuance_rate : list byte;
      coupon_rate : list byte;
      monthly_cycle_of_coupon_payment : list byte;
      coupon_payment_timing_code : list byte;
      interest_payment : list byte;
      coupon_payment_date_type_code : list byte;
      decimal_point_of_coupon_type_code : list byte;
      pre_issue_sale_coupon_payment_type_code : list byte;
      issuing_amount : list byte;
      listed_amount : list byte;
      redemption_ratio_at_maturity : list byte;
      amortization_type_code : list byte;
      number_of_months_for_grace : list byte;
      number_of_amortization : list byte;
      trading_halt : list byte;
      prior_coupon_payment_date : list byte;
      next_coupon_payment_date : list byte;
      perpetual_bond_maturity_structure_status : list byte;
      strip_bond_type_code : list byte;
      base_price : list byte;
      liquidation_trade : list byte;
      investment_caution_bond_type_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (total_number_of_instruments_of_the_contract record) = 6 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (retail_bond_type_code record) = 2 /\
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (abbreviated_issue_name_in_en record) = 40 /\
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (bond_listing_type_code record) = 1 /\
      Datatypes.length (bond_category_code record) = 6 /\
      Datatypes.length (bond_guaranteed_type_code record) = 1 /\
      Datatypes.length (coupon_payment_type_code record) = 2 /\
      Datatypes.length (listing_date record) = 8 /\
      Datatypes.length (issue_date record) = 8 /\
      Datatypes.length (redemption_date record) = 8 /\
      Datatypes.length (sale_date record) = 8 /\
      Datatypes.length (bond_issuance_rate record) = 13 /\
      Datatypes.length (coupon_rate record) = 14 /\
      Datatypes.length (monthly_cycle_of_coupon_payment record) = 4 /\
      Datatypes.length (coupon_payment_timing_code record) = 1 /\
      Datatypes.length (interest_payment record) = 1 /\
      Datatypes.length (coupon_payment_date_type_code record) = 1 /\
      Datatypes.length (decimal_point_of_coupon_type_code record) = 1 /\
      Datatypes.length (pre_issue_sale_coupon_payment_type_code record) = 1 /\
      Datatypes.length (issuing_amount record) = 22 /\
      Datatypes.length (listed_amount record) = 22 /\
      Datatypes.length (redemption_ratio_at_maturity record) = 13 /\
      Datatypes.length (amortization_type_code record) = 1 /\
      Datatypes.length (number_of_months_for_grace record) = 4 /\
      Datatypes.length (number_of_amortization record) = 5 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (prior_coupon_payment_date record) = 8 /\
      Datatypes.length (next_coupon_payment_date record) = 8 /\
      Datatypes.length (perpetual_bond_maturity_structure_status record) = 1 /\
      Datatypes.length (strip_bond_type_code record) = 1 /\
      Datatypes.length (base_price record) = 11 /\
      Datatypes.length (liquidation_trade record) = 1 /\
      Datatypes.length (investment_caution_bond_type_code record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 6 (total_number_of_instruments_of_the_contract record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 2 (retail_bond_type_code record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name_in_en record) ++
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 1 (bond_listing_type_code record) ++
      encode_bytes 6 (bond_category_code record) ++
      encode_bytes 1 (bond_guaranteed_type_code record) ++
      encode_bytes 2 (coupon_payment_type_code record) ++
      encode_bytes 8 (listing_date record) ++
      encode_bytes 8 (issue_date record) ++
      encode_bytes 8 (redemption_date record) ++
      encode_bytes 8 (sale_date record) ++
      encode_bytes 13 (bond_issuance_rate record) ++
      encode_bytes 14 (coupon_rate record) ++
      encode_bytes 4 (monthly_cycle_of_coupon_payment record) ++
      encode_bytes 1 (coupon_payment_timing_code record) ++
      encode_bytes 1 (interest_payment record) ++
      encode_bytes 1 (coupon_payment_date_type_code record) ++
      encode_bytes 1 (decimal_point_of_coupon_type_code record) ++
      encode_bytes 1 (pre_issue_sale_coupon_payment_type_code record) ++
      encode_bytes 22 (issuing_amount record) ++
      encode_bytes 22 (listed_amount record) ++
      encode_bytes 13 (redemption_ratio_at_maturity record) ++
      encode_bytes 1 (amortization_type_code record) ++
      encode_bytes 4 (number_of_months_for_grace record) ++
      encode_bytes 5 (number_of_amortization record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 8 (prior_coupon_payment_date record) ++
      encode_bytes 8 (next_coupon_payment_date record) ++
      encode_bytes 1 (perpetual_bond_maturity_structure_status record) ++
      encode_bytes 1 (strip_bond_type_code record) ++
      encode_bytes 11 (base_price record) ++
      encode_bytes 1 (liquidation_trade record) ++
      encode_bytes 1 (investment_caution_bond_type_code record) ++
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
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (retail_bond_type_code_value, bytes) =>
                              match decode_bytes 40 bytes with
                              | None => None
                              | Some (abbreviated_issue_name_value, bytes) =>
                                  match decode_bytes 40 bytes with
                                  | None => None
                                  | Some (abbreviated_issue_name_in_en_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (market_operation_product_id_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (bond_listing_type_code_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (bond_category_code_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (bond_guaranteed_type_code_value, bytes) =>
                                                      match decode_bytes 2 bytes with
                                                      | None => None
                                                      | Some (coupon_payment_type_code_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (listing_date_value, bytes) =>
                                                              match decode_bytes 8 bytes with
                                                              | None => None
                                                              | Some (issue_date_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (redemption_date_value, bytes) =>
                                                                      match decode_bytes 8 bytes with
                                                                      | None => None
                                                                      | Some (sale_date_value, bytes) =>
                                                                          match decode_bytes 13 bytes with
                                                                          | None => None
                                                                          | Some (bond_issuance_rate_value, bytes) =>
                                                                              match decode_bytes 14 bytes with
                                                                              | None => None
                                                                              | Some (coupon_rate_value, bytes) =>
                                                                                  match decode_bytes 4 bytes with
                                                                                  | None => None
                                                                                  | Some (monthly_cycle_of_coupon_payment_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (coupon_payment_timing_code_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (interest_payment_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (coupon_payment_date_type_code_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (decimal_point_of_coupon_type_code_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (pre_issue_sale_coupon_payment_type_code_value, bytes) =>
                                                                                                          match decode_bytes 22 bytes with
                                                                                                          | None => None
                                                                                                          | Some (issuing_amount_value, bytes) =>
                                                                                                              match decode_bytes 22 bytes with
                                                                                                              | None => None
                                                                                                              | Some (listed_amount_value, bytes) =>
                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (redemption_ratio_at_maturity_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (amortization_type_code_value, bytes) =>
                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (number_of_months_for_grace_value, bytes) =>
                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (number_of_amortization_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (trading_halt_value, bytes) =>
                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (prior_coupon_payment_date_value, bytes) =>
                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (next_coupon_payment_date_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (perpetual_bond_maturity_structure_status_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (strip_bond_type_code_value, bytes) =>
                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (base_price_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (liquidation_trade_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (investment_caution_bond_type_code_value, bytes) =>
                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; total_number_of_instruments_of_the_contract := total_number_of_instruments_of_the_contract_value; business_date := business_date_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; retail_bond_type_code := retail_bond_type_code_value; abbreviated_issue_name := abbreviated_issue_name_value; abbreviated_issue_name_in_en := abbreviated_issue_name_in_en_value; market_operation_product_id := market_operation_product_id_value; bond_listing_type_code := bond_listing_type_code_value; bond_category_code := bond_category_code_value; bond_guaranteed_type_code := bond_guaranteed_type_code_value; coupon_payment_type_code := coupon_payment_type_code_value; listing_date := listing_date_value; issue_date := issue_date_value; redemption_date := redemption_date_value; sale_date := sale_date_value; bond_issuance_rate := bond_issuance_rate_value; coupon_rate := coupon_rate_value; monthly_cycle_of_coupon_payment := monthly_cycle_of_coupon_payment_value; coupon_payment_timing_code := coupon_payment_timing_code_value; interest_payment := interest_payment_value; coupon_payment_date_type_code := coupon_payment_date_type_code_value; decimal_point_of_coupon_type_code := decimal_point_of_coupon_type_code_value; pre_issue_sale_coupon_payment_type_code := pre_issue_sale_coupon_payment_type_code_value; issuing_amount := issuing_amount_value; listed_amount := listed_amount_value; redemption_ratio_at_maturity := redemption_ratio_at_maturity_value; amortization_type_code := amortization_type_code_value; number_of_months_for_grace := number_of_months_for_grace_value; number_of_amortization := number_of_amortization_value; trading_halt := trading_halt_value; prior_coupon_payment_date := prior_coupon_payment_date_value; next_coupon_payment_date := next_coupon_payment_date_value; perpetual_bond_maturity_structure_status := perpetual_bond_maturity_structure_status_value; strip_bond_type_code := strip_bond_type_code_value; base_price := base_price_value; liquidation_trade := liquidation_trade_value; investment_caution_bond_type_code := investment_caution_bond_type_code_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 303.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 bound_39]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_39.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondsBatchDataMessage.

  Module RepoBatchDataMessage.

    (** REPO Batch Data. Per-issue reference data dumped at start-of-day for REPO instruments. *)
    Record t := {
      message_sequence_number : list byte;
      total_number_of_instruments_of_the_contract : list byte;
      business_date : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      market_operation_product_id : list byte;
      abbreviated_issue_name : list byte;
      market_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (total_number_of_instruments_of_the_contract record) = 6 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (market_value record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 6 (total_number_of_instruments_of_the_contract record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 11 (market_value record) ++
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
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (market_operation_product_id_value, bytes) =>
                              match decode_bytes 40 bytes with
                              | None => None
                              | Some (abbreviated_issue_name_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (market_value_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (end_keyword_value, bytes) =>
                                          Some ({| message_sequence_number := message_sequence_number_value; total_number_of_instruments_of_the_contract := total_number_of_instruments_of_the_contract_value; business_date := business_date_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; market_operation_product_id := market_operation_product_id_value; abbreviated_issue_name := abbreviated_issue_name_value; market_value := market_value_value; end_keyword := end_keyword_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 95.
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

  End RepoBatchDataMessage.

  Module IssueEventMessage.

    (** Issue Event. Per-issue lifecycle event log. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      event_type_code : list byte;
      event_reason_code : list byte;
      event_start_date : list byte;
      event_end_date : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (event_type_code record) = 2 /\
      Datatypes.length (event_reason_code record) = 4 /\
      Datatypes.length (event_start_date record) = 8 /\
      Datatypes.length (event_end_date record) = 8 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 2 (event_type_code record) ++
      encode_bytes 4 (event_reason_code record) ++
      encode_bytes 8 (event_start_date record) ++
      encode_bytes 8 (event_end_date record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (event_type_code_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (event_reason_code_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (event_start_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (event_end_date_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; event_type_code := event_type_code_value; event_reason_code := event_reason_code_value; event_start_date := event_start_date_value; event_end_date := event_end_date_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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

  End IssueEventMessage.

  Module CorporateBondsReferenceMessage.

    (** Corporate Bonds related to Securities and Baby Bonds Issue reference data. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      abbreviated_issue_name : list byte;
      issue_date : list byte;
      redemption_date : list byte;
      listing_date : list byte;
      coupon_payment_type_code : list byte;
      issuing_amount : list byte;
      listed_amount : list byte;
      coupon_payment_timing_code : list byte;
      number_of_months_for_grace : list byte;
      number_of_amortization : list byte;
      interest_payment : list byte;
      coupon_payment_date_type_code : list byte;
      coupon_rate : list byte;
      substitute_price_of_securities : list byte;
      isin : list byte;
      date_to_start_exercising : list byte;
      date_to_end_exercising : list byte;
      record_date_of_dividend_payout : list byte;
      exercise_ratio : list byte;
      yield_to_maturity : list byte;
      corporate_bonds_related_to_securities_exercise_price : list byte;
      abbreviated_issue_code : list byte;
      baby_bonds_type_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (issue_date record) = 8 /\
      Datatypes.length (redemption_date record) = 8 /\
      Datatypes.length (listing_date record) = 8 /\
      Datatypes.length (coupon_payment_type_code record) = 2 /\
      Datatypes.length (issuing_amount record) = 22 /\
      Datatypes.length (listed_amount record) = 22 /\
      Datatypes.length (coupon_payment_timing_code record) = 1 /\
      Datatypes.length (number_of_months_for_grace record) = 4 /\
      Datatypes.length (number_of_amortization record) = 5 /\
      Datatypes.length (interest_payment record) = 1 /\
      Datatypes.length (coupon_payment_date_type_code record) = 1 /\
      Datatypes.length (coupon_rate record) = 14 /\
      Datatypes.length (substitute_price_of_securities record) = 11 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (date_to_start_exercising record) = 8 /\
      Datatypes.length (date_to_end_exercising record) = 8 /\
      Datatypes.length (record_date_of_dividend_payout record) = 1 /\
      Datatypes.length (exercise_ratio record) = 7 /\
      Datatypes.length (yield_to_maturity record) = 13 /\
      Datatypes.length (corporate_bonds_related_to_securities_exercise_price record) = 11 /\
      Datatypes.length (abbreviated_issue_code record) = 9 /\
      Datatypes.length (baby_bonds_type_code record) = 3 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 8 (issue_date record) ++
      encode_bytes 8 (redemption_date record) ++
      encode_bytes 8 (listing_date record) ++
      encode_bytes 2 (coupon_payment_type_code record) ++
      encode_bytes 22 (issuing_amount record) ++
      encode_bytes 22 (listed_amount record) ++
      encode_bytes 1 (coupon_payment_timing_code record) ++
      encode_bytes 4 (number_of_months_for_grace record) ++
      encode_bytes 5 (number_of_amortization record) ++
      encode_bytes 1 (interest_payment record) ++
      encode_bytes 1 (coupon_payment_date_type_code record) ++
      encode_bytes 14 (coupon_rate record) ++
      encode_bytes 11 (substitute_price_of_securities record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (date_to_start_exercising record) ++
      encode_bytes 8 (date_to_end_exercising record) ++
      encode_bytes 1 (record_date_of_dividend_payout record) ++
      encode_bytes 7 (exercise_ratio record) ++
      encode_bytes 13 (yield_to_maturity record) ++
      encode_bytes 11 (corporate_bonds_related_to_securities_exercise_price record) ++
      encode_bytes 9 (abbreviated_issue_code record) ++
      encode_bytes 3 (baby_bonds_type_code record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 40 bytes with
              | None => None
              | Some (abbreviated_issue_name_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (issue_date_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (redemption_date_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (listing_date_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (coupon_payment_type_code_value, bytes) =>
                                  match decode_bytes 22 bytes with
                                  | None => None
                                  | Some (issuing_amount_value, bytes) =>
                                      match decode_bytes 22 bytes with
                                      | None => None
                                      | Some (listed_amount_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (coupon_payment_timing_code_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (number_of_months_for_grace_value, bytes) =>
                                                  match decode_bytes 5 bytes with
                                                  | None => None
                                                  | Some (number_of_amortization_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (interest_payment_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (coupon_payment_date_type_code_value, bytes) =>
                                                              match decode_bytes 14 bytes with
                                                              | None => None
                                                              | Some (coupon_rate_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (substitute_price_of_securities_value, bytes) =>
                                                                      match decode_bytes 12 bytes with
                                                                      | None => None
                                                                      | Some (isin_value, bytes) =>
                                                                          match decode_bytes 8 bytes with
                                                                          | None => None
                                                                          | Some (date_to_start_exercising_value, bytes) =>
                                                                              match decode_bytes 8 bytes with
                                                                              | None => None
                                                                              | Some (date_to_end_exercising_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (record_date_of_dividend_payout_value, bytes) =>
                                                                                      match decode_bytes 7 bytes with
                                                                                      | None => None
                                                                                      | Some (exercise_ratio_value, bytes) =>
                                                                                          match decode_bytes 13 bytes with
                                                                                          | None => None
                                                                                          | Some (yield_to_maturity_value, bytes) =>
                                                                                              match decode_bytes 11 bytes with
                                                                                              | None => None
                                                                                              | Some (corporate_bonds_related_to_securities_exercise_price_value, bytes) =>
                                                                                                  match decode_bytes 9 bytes with
                                                                                                  | None => None
                                                                                                  | Some (abbreviated_issue_code_value, bytes) =>
                                                                                                      match decode_bytes 3 bytes with
                                                                                                      | None => None
                                                                                                      | Some (baby_bonds_type_code_value, bytes) =>
                                                                                                          match decode_uint 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; abbreviated_issue_name := abbreviated_issue_name_value; issue_date := issue_date_value; redemption_date := redemption_date_value; listing_date := listing_date_value; coupon_payment_type_code := coupon_payment_type_code_value; issuing_amount := issuing_amount_value; listed_amount := listed_amount_value; coupon_payment_timing_code := coupon_payment_timing_code_value; number_of_months_for_grace := number_of_months_for_grace_value; number_of_amortization := number_of_amortization_value; interest_payment := interest_payment_value; coupon_payment_date_type_code := coupon_payment_date_type_code_value; coupon_rate := coupon_rate_value; substitute_price_of_securities := substitute_price_of_securities_value; isin := isin_value; date_to_start_exercising := date_to_start_exercising_value; date_to_end_exercising := date_to_end_exercising_value; record_date_of_dividend_payout := record_date_of_dividend_payout_value; exercise_ratio := exercise_ratio_value; yield_to_maturity := yield_to_maturity_value; corporate_bonds_related_to_securities_exercise_price := corporate_bonds_related_to_securities_exercise_price_value; abbreviated_issue_code := abbreviated_issue_code_value; baby_bonds_type_code := baby_bonds_type_code_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 240.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CorporateBondsReferenceMessage.

  Module RegularBondsInstallmentRepaymentDateMessage.

    (** Regular Bonds installment repayment date. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      installment_repayment_date : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (installment_repayment_date record) = 8 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (installment_repayment_date record) ++
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
              | Some (installment_repayment_date_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (end_keyword_value, bytes) =>
                      Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; installment_repayment_date := installment_repayment_date_value; end_keyword := end_keyword_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegularBondsInstallmentRepaymentDateMessage.

  Module RepoClassificationDataMessage.

    (** REPO Classification Data. *)
    Record t := {
      message_sequence_number : list byte;
      business_date : list byte;
      repo_classification_code : list byte;
      repo_classification_name : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (repo_classification_code record) = 2 /\
      Datatypes.length (repo_classification_name record) = 20 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 2 (repo_classification_code record) ++
      encode_bytes 20 (repo_classification_name record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (business_date_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (repo_classification_code_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (repo_classification_name_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| message_sequence_number := message_sequence_number_value; business_date := business_date_value; repo_classification_code := repo_classification_code_value; repo_classification_name := repo_classification_name_value; end_keyword := end_keyword_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RepoClassificationDataMessage.

  Module RepoTradeAvailabilityPerTermMessage.

    (** REPO Trade Availability per Term. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      number_of_repo_trade_periods : list byte;
      repo_trade_period_1 : list byte;
      repo_trade_period_2 : list byte;
      repo_trade_period_3 : list byte;
      repo_trade_period_4 : list byte;
      repo_trade_period_5 : list byte;
      repo_trade_period_6 : list byte;
      repo_trade_period_7 : list byte;
      repo_trade_period_8 : list byte;
      repo_trade_period_9 : list byte;
      repo_trade_period_10 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (number_of_repo_trade_periods record) = 3 /\
      Datatypes.length (repo_trade_period_1 record) = 3 /\
      Datatypes.length (repo_trade_period_2 record) = 3 /\
      Datatypes.length (repo_trade_period_3 record) = 3 /\
      Datatypes.length (repo_trade_period_4 record) = 3 /\
      Datatypes.length (repo_trade_period_5 record) = 3 /\
      Datatypes.length (repo_trade_period_6 record) = 3 /\
      Datatypes.length (repo_trade_period_7 record) = 3 /\
      Datatypes.length (repo_trade_period_8 record) = 3 /\
      Datatypes.length (repo_trade_period_9 record) = 3 /\
      Datatypes.length (repo_trade_period_10 record) = 3 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 3 (number_of_repo_trade_periods record) ++
      encode_bytes 3 (repo_trade_period_1 record) ++
      encode_bytes 3 (repo_trade_period_2 record) ++
      encode_bytes 3 (repo_trade_period_3 record) ++
      encode_bytes 3 (repo_trade_period_4 record) ++
      encode_bytes 3 (repo_trade_period_5 record) ++
      encode_bytes 3 (repo_trade_period_6 record) ++
      encode_bytes 3 (repo_trade_period_7 record) ++
      encode_bytes 3 (repo_trade_period_8 record) ++
      encode_bytes 3 (repo_trade_period_9 record) ++
      encode_bytes 3 (repo_trade_period_10 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (number_of_repo_trade_periods_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (repo_trade_period_1_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (repo_trade_period_2_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (repo_trade_period_3_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (repo_trade_period_4_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (repo_trade_period_5_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (repo_trade_period_6_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (repo_trade_period_7_value, bytes) =>
                                              match decode_bytes 3 bytes with
                                              | None => None
                                              | Some (repo_trade_period_8_value, bytes) =>
                                                  match decode_bytes 3 bytes with
                                                  | None => None
                                                  | Some (repo_trade_period_9_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (repo_trade_period_10_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (end_keyword_value, bytes) =>
                                                              Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; number_of_repo_trade_periods := number_of_repo_trade_periods_value; repo_trade_period_1 := repo_trade_period_1_value; repo_trade_period_2 := repo_trade_period_2_value; repo_trade_period_3 := repo_trade_period_3_value; repo_trade_period_4 := repo_trade_period_4_value; repo_trade_period_5 := repo_trade_period_5_value; repo_trade_period_6 := repo_trade_period_6_value; repo_trade_period_7 := repo_trade_period_7_value; repo_trade_period_8 := repo_trade_period_8_value; repo_trade_period_9 := repo_trade_period_9_value; repo_trade_period_10 := repo_trade_period_10_value; end_keyword := end_keyword_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

  End RepoTradeAvailabilityPerTermMessage.

  Module RetailBondsTypeCodeMessage.

    (** Retail Bonds Type Code reference (IFMSBTD0018) — Bonds A BND variant. *)
    Record t := {
      message_sequence_number : list byte;
      retail_bond_type_code : list byte;
      retail_bond_category_name : list byte;
      retail_bond_category_name_in_en : list byte;
      retail_bond_generated_quotes : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (retail_bond_type_code record) = 2 /\
      Datatypes.length (retail_bond_category_name record) = 20 /\
      Datatypes.length (retail_bond_category_name_in_en record) = 20 /\
      Datatypes.length (retail_bond_generated_quotes record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (retail_bond_type_code record) ++
      encode_bytes 20 (retail_bond_category_name record) ++
      encode_bytes 20 (retail_bond_category_name_in_en record) ++
      encode_bytes 1 (retail_bond_generated_quotes record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (retail_bond_type_code_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (retail_bond_category_name_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (retail_bond_category_name_in_en_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (retail_bond_generated_quotes_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| message_sequence_number := message_sequence_number_value; retail_bond_type_code := retail_bond_type_code_value; retail_bond_category_name := retail_bond_category_name_value; retail_bond_category_name_in_en := retail_bond_category_name_in_en_value; retail_bond_generated_quotes := retail_bond_generated_quotes_value; end_keyword := end_keyword_value |}, bytes)
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

  End RetailBondsTypeCodeMessage.

End KoscomMdcsRealtimeSecuritiesBV2018.
