From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Koscom Co., Ltd. MDCS Realtime Bond A

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

Module KoscomMdcsRealtimeBondAV2020.

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
      Datatypes.length (calculation_time record) = 9 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (index_change_sign_against_the_previous_day record) = 1 /\
      Datatypes.length (index_change_against_the_previous_day record) = 9 /\
      Datatypes.length (accumulated_trading_volume record) = 15 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 9 (calculation_time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (index_change_sign_against_the_previous_day record) ++
      encode_bytes 9 (index_change_against_the_previous_day record) ++
      encode_bytes 15 (accumulated_trading_volume record) ++
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
              match decode_bytes 9 bytes with
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
                              match decode_bytes 15 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 88.
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
      Datatypes.length (calculation_time record) = 9 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (index_change_sign_against_the_previous_day record) = 1 /\
      Datatypes.length (index_change_against_the_previous_day record) = 9 /\
      Datatypes.length (accumulated_trading_volume record) = 15 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 9 (calculation_time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (index_change_sign_against_the_previous_day record) ++
      encode_bytes 9 (index_change_against_the_previous_day record) ++
      encode_bytes 15 (accumulated_trading_volume record) ++
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
              match decode_bytes 9 bytes with
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
                              match decode_bytes 15 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 88.
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
      Datatypes.length (calculation_time record) = 9 /\
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
      encode_bytes 9 (calculation_time record) ++
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
                  match decode_bytes 9 bytes with
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
      Datatypes.length (transmission_time record) = 9 /\
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
      encode_bytes 9 (transmission_time record) ++
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
                                                          match decode_bytes 9 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 178.
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

  Module MarketOperationTsMessage.

    (** Market Operation TS. Reports per-issue when a Market Operation event occurs (halts, resumes, expirations). Information Category byte 3 selects market (K=KTB, B=Bonds, M=Baby Bonds, R=REPO, S=KOSPI, Q=KOSDAQ, X=KONEX, G=Gold, E=Emissions, F=Derivatives). *)
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

  End MarketOperationTsMessage.

  Module MarketOperationScheduleMessage.

    (** Market Operation Schedule. Reports session-level schedule and configuration changes. *)
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

  End MarketOperationScheduleMessage.

  Module IssueClosingMessage.

    (** Bonds Issue Closing. Reports per-issue closing event with closing price. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      duration_of_term_repo : list byte;
      closing_price : list byte;
      closing_price_yield : list byte;
      closing_price_type_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (duration_of_term_repo record) = 4 /\
      Datatypes.length (closing_price record) = 11 /\
      Datatypes.length (closing_price_yield record) = 13 /\
      Datatypes.length (closing_price_type_code record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 4 (duration_of_term_repo record) ++
      encode_bytes 11 (closing_price record) ++
      encode_bytes 13 (closing_price_yield record) ++
      encode_bytes 1 (closing_price_type_code record) ++
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
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (duration_of_term_repo_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (closing_price_yield_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (closing_price_type_code_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; duration_of_term_repo := duration_of_term_repo_value; closing_price := closing_price_value; closing_price_yield := closing_price_yield_value; closing_price_type_code := closing_price_type_code_value; end_keyword := end_keyword_value |}, bytes)
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

  End IssueClosingMessage.

  Module MemberFirmSanctionsMessage.

    (** Member firm imposing/lifting of sanctions. Information Category byte 3 selects market. *)
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

  End MemberFirmSanctionsMessage.

  Module RegularBondsKtbQuoteMessage.

    (** Regular Bonds and KTB Quote. Multi-level bid/ask quotes and remaining quantities. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      processing_time_of_trading_system : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_remaining_quantity : list byte;
      bid_level_1_remaining_quantity : list byte;
      ask_level_1_yield : list byte;
      bid_level_1_yield : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_remaining_quantity : list byte;
      bid_level_2_remaining_quantity : list byte;
      ask_level_2_yield : list byte;
      bid_level_2_yield : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_remaining_quantity : list byte;
      bid_level_3_remaining_quantity : list byte;
      ask_level_3_yield : list byte;
      bid_level_3_yield : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_remaining_quantity : list byte;
      bid_level_4_remaining_quantity : list byte;
      ask_level_4_yield : list byte;
      bid_level_4_yield : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_remaining_quantity : list byte;
      bid_level_5_remaining_quantity : list byte;
      ask_level_5_yield : list byte;
      bid_level_5_yield : list byte;
      ask_total_remaining_quantity : list byte;
      bid_total_remaining_quantity : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_1_yield record) = 13 /\
      Datatypes.length (bid_level_1_yield record) = 13 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_2_yield record) = 13 /\
      Datatypes.length (bid_level_2_yield record) = 13 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_3_yield record) = 13 /\
      Datatypes.length (bid_level_3_yield record) = 13 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_4_yield record) = 13 /\
      Datatypes.length (bid_level_4_yield record) = 13 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_5_yield record) = 13 /\
      Datatypes.length (bid_level_5_yield record) = 13 /\
      Datatypes.length (ask_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_total_remaining_quantity record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 15 (ask_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_level_1_remaining_quantity record) ++
      encode_bytes 13 (ask_level_1_yield record) ++
      encode_bytes 13 (bid_level_1_yield record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 15 (ask_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_level_2_remaining_quantity record) ++
      encode_bytes 13 (ask_level_2_yield record) ++
      encode_bytes 13 (bid_level_2_yield record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 15 (ask_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_level_3_remaining_quantity record) ++
      encode_bytes 13 (ask_level_3_yield record) ++
      encode_bytes 13 (bid_level_3_yield record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 15 (ask_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_level_4_remaining_quantity record) ++
      encode_bytes 13 (ask_level_4_yield record) ++
      encode_bytes 13 (bid_level_4_yield record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 15 (ask_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_level_5_remaining_quantity record) ++
      encode_bytes 13 (ask_level_5_yield record) ++
      encode_bytes 13 (bid_level_5_yield record) ++
      encode_bytes 15 (ask_total_remaining_quantity record) ++
      encode_bytes 15 (bid_total_remaining_quantity record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (ask_level_1_price_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (bid_level_1_price_value, bytes) =>
                                  match decode_bytes 15 bytes with
                                  | None => None
                                  | Some (ask_level_1_remaining_quantity_value, bytes) =>
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (bid_level_1_remaining_quantity_value, bytes) =>
                                          match decode_bytes 13 bytes with
                                          | None => None
                                          | Some (ask_level_1_yield_value, bytes) =>
                                              match decode_bytes 13 bytes with
                                              | None => None
                                              | Some (bid_level_1_yield_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (ask_level_2_price_value, bytes) =>
                                                      match decode_bytes 11 bytes with
                                                      | None => None
                                                      | Some (bid_level_2_price_value, bytes) =>
                                                          match decode_bytes 15 bytes with
                                                          | None => None
                                                          | Some (ask_level_2_remaining_quantity_value, bytes) =>
                                                              match decode_bytes 15 bytes with
                                                              | None => None
                                                              | Some (bid_level_2_remaining_quantity_value, bytes) =>
                                                                  match decode_bytes 13 bytes with
                                                                  | None => None
                                                                  | Some (ask_level_2_yield_value, bytes) =>
                                                                      match decode_bytes 13 bytes with
                                                                      | None => None
                                                                      | Some (bid_level_2_yield_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (ask_level_3_price_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (bid_level_3_price_value, bytes) =>
                                                                                  match decode_bytes 15 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_3_remaining_quantity_value, bytes) =>
                                                                                      match decode_bytes 15 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_3_remaining_quantity_value, bytes) =>
                                                                                          match decode_bytes 13 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_3_yield_value, bytes) =>
                                                                                              match decode_bytes 13 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_3_yield_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_4_price_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_4_price_value, bytes) =>
                                                                                                          match decode_bytes 15 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_4_remaining_quantity_value, bytes) =>
                                                                                                              match decode_bytes 15 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_4_remaining_quantity_value, bytes) =>
                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_4_yield_value, bytes) =>
                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_4_yield_value, bytes) =>
                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_5_price_value, bytes) =>
                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_5_yield_value, bytes) =>
                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_5_yield_value, bytes) =>
                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_total_remaining_quantity_value, bytes) =>
                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_total_remaining_quantity_value, bytes) =>
                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_remaining_quantity := ask_level_1_remaining_quantity_value; bid_level_1_remaining_quantity := bid_level_1_remaining_quantity_value; ask_level_1_yield := ask_level_1_yield_value; bid_level_1_yield := bid_level_1_yield_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_remaining_quantity := ask_level_2_remaining_quantity_value; bid_level_2_remaining_quantity := bid_level_2_remaining_quantity_value; ask_level_2_yield := ask_level_2_yield_value; bid_level_2_yield := bid_level_2_yield_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_remaining_quantity := ask_level_3_remaining_quantity_value; bid_level_3_remaining_quantity := bid_level_3_remaining_quantity_value; ask_level_3_yield := ask_level_3_yield_value; bid_level_3_yield := bid_level_3_yield_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_remaining_quantity := ask_level_4_remaining_quantity_value; bid_level_4_remaining_quantity := bid_level_4_remaining_quantity_value; ask_level_4_yield := ask_level_4_yield_value; bid_level_4_yield := bid_level_4_yield_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_remaining_quantity := ask_level_5_remaining_quantity_value; bid_level_5_remaining_quantity := bid_level_5_remaining_quantity_value; ask_level_5_yield := ask_level_5_yield_value; bid_level_5_yield := bid_level_5_yield_value; ask_total_remaining_quantity := ask_total_remaining_quantity_value; bid_total_remaining_quantity := bid_total_remaining_quantity_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 457.
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

  End RegularBondsKtbQuoteMessage.

  Module BondsOrderFilledMessage.

    (** Bonds Order Filled. Trade prints for KTB, Baby Bonds, and General Bonds. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      trading_date : list byte;
      trading_value : list byte;
      bond_yield : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      yield_opening_price : list byte;
      yield_todays_high : list byte;
      yield_todays_low : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      settlement_date : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (trading_value record) = 22 /\
      Datatypes.length (bond_yield record) = 13 /\
      Datatypes.length (opening_price record) = 11 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (yield_opening_price record) = 13 /\
      Datatypes.length (yield_todays_high record) = 13 /\
      Datatypes.length (yield_todays_low record) = 13 /\
      Datatypes.length (accumulated_trading_volume record) = 15 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (settlement_date record) = 8 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 22 (trading_value record) ++
      encode_bytes 13 (bond_yield record) ++
      encode_bytes 11 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 13 (yield_opening_price record) ++
      encode_bytes 13 (yield_todays_high record) ++
      encode_bytes 13 (yield_todays_low record) ++
      encode_bytes 15 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 8 (settlement_date record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (trading_price_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (trading_volume_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (trading_date_value, bytes) =>
                                      match decode_bytes 22 bytes with
                                      | None => None
                                      | Some (trading_value_value, bytes) =>
                                          match decode_bytes 13 bytes with
                                          | None => None
                                          | Some (bond_yield_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (opening_price_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (todays_high_value, bytes) =>
                                                      match decode_bytes 11 bytes with
                                                      | None => None
                                                      | Some (todays_low_value, bytes) =>
                                                          match decode_bytes 13 bytes with
                                                          | None => None
                                                          | Some (yield_opening_price_value, bytes) =>
                                                              match decode_bytes 13 bytes with
                                                              | None => None
                                                              | Some (yield_todays_high_value, bytes) =>
                                                                  match decode_bytes 13 bytes with
                                                                  | None => None
                                                                  | Some (yield_todays_low_value, bytes) =>
                                                                      match decode_bytes 15 bytes with
                                                                      | None => None
                                                                      | Some (accumulated_trading_volume_value, bytes) =>
                                                                          match decode_bytes 22 bytes with
                                                                          | None => None
                                                                          | Some (accumulated_trading_value_value, bytes) =>
                                                                              match decode_bytes 8 bytes with
                                                                              | None => None
                                                                              | Some (settlement_date_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; trading_date := trading_date_value; trading_value := trading_value_value; bond_yield := bond_yield_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; yield_opening_price := yield_opening_price_value; yield_todays_high := yield_todays_high_value; yield_todays_low := yield_todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; settlement_date := settlement_date_value; end_keyword := end_keyword_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 218.
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

  End BondsOrderFilledMessage.

  Module GeneralBondsKtbOrderFilledPlusQuoteMessage.

    (** General Bonds and KTB Order Filled plus Quote. Trade print followed by full multi-level quote state. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      trading_date : list byte;
      trading_value : list byte;
      bond_yield : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      yield_opening_price : list byte;
      yield_todays_high : list byte;
      yield_todays_low : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      settlement_date : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_remaining_quantity : list byte;
      bid_level_1_remaining_quantity : list byte;
      ask_level_1_yield : list byte;
      bid_level_1_yield : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_remaining_quantity : list byte;
      bid_level_2_remaining_quantity : list byte;
      ask_level_2_yield : list byte;
      bid_level_2_yield : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_remaining_quantity : list byte;
      bid_level_3_remaining_quantity : list byte;
      ask_level_3_yield : list byte;
      bid_level_3_yield : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_remaining_quantity : list byte;
      bid_level_4_remaining_quantity : list byte;
      ask_level_4_yield : list byte;
      bid_level_4_yield : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_remaining_quantity : list byte;
      bid_level_5_remaining_quantity : list byte;
      ask_level_5_yield : list byte;
      bid_level_5_yield : list byte;
      ask_total_remaining_quantity : list byte;
      bid_total_remaining_quantity : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (trading_value record) = 22 /\
      Datatypes.length (bond_yield record) = 13 /\
      Datatypes.length (opening_price record) = 11 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (yield_opening_price record) = 13 /\
      Datatypes.length (yield_todays_high record) = 13 /\
      Datatypes.length (yield_todays_low record) = 13 /\
      Datatypes.length (accumulated_trading_volume record) = 15 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (settlement_date record) = 8 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_1_yield record) = 13 /\
      Datatypes.length (bid_level_1_yield record) = 13 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_2_yield record) = 13 /\
      Datatypes.length (bid_level_2_yield record) = 13 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_3_yield record) = 13 /\
      Datatypes.length (bid_level_3_yield record) = 13 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_4_yield record) = 13 /\
      Datatypes.length (bid_level_4_yield record) = 13 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_5_yield record) = 13 /\
      Datatypes.length (bid_level_5_yield record) = 13 /\
      Datatypes.length (ask_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_total_remaining_quantity record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 22 (trading_value record) ++
      encode_bytes 13 (bond_yield record) ++
      encode_bytes 11 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 13 (yield_opening_price record) ++
      encode_bytes 13 (yield_todays_high record) ++
      encode_bytes 13 (yield_todays_low record) ++
      encode_bytes 15 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 8 (settlement_date record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 15 (ask_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_level_1_remaining_quantity record) ++
      encode_bytes 13 (ask_level_1_yield record) ++
      encode_bytes 13 (bid_level_1_yield record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 15 (ask_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_level_2_remaining_quantity record) ++
      encode_bytes 13 (ask_level_2_yield record) ++
      encode_bytes 13 (bid_level_2_yield record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 15 (ask_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_level_3_remaining_quantity record) ++
      encode_bytes 13 (ask_level_3_yield record) ++
      encode_bytes 13 (bid_level_3_yield record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 15 (ask_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_level_4_remaining_quantity record) ++
      encode_bytes 13 (ask_level_4_yield record) ++
      encode_bytes 13 (bid_level_4_yield record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 15 (ask_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_level_5_remaining_quantity record) ++
      encode_bytes 13 (ask_level_5_yield record) ++
      encode_bytes 13 (bid_level_5_yield record) ++
      encode_bytes 15 (ask_total_remaining_quantity record) ++
      encode_bytes 15 (bid_total_remaining_quantity record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (trading_price_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (trading_volume_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (trading_date_value, bytes) =>
                                      match decode_bytes 22 bytes with
                                      | None => None
                                      | Some (trading_value_value, bytes) =>
                                          match decode_bytes 13 bytes with
                                          | None => None
                                          | Some (bond_yield_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (opening_price_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (todays_high_value, bytes) =>
                                                      match decode_bytes 11 bytes with
                                                      | None => None
                                                      | Some (todays_low_value, bytes) =>
                                                          match decode_bytes 13 bytes with
                                                          | None => None
                                                          | Some (yield_opening_price_value, bytes) =>
                                                              match decode_bytes 13 bytes with
                                                              | None => None
                                                              | Some (yield_todays_high_value, bytes) =>
                                                                  match decode_bytes 13 bytes with
                                                                  | None => None
                                                                  | Some (yield_todays_low_value, bytes) =>
                                                                      match decode_bytes 15 bytes with
                                                                      | None => None
                                                                      | Some (accumulated_trading_volume_value, bytes) =>
                                                                          match decode_bytes 22 bytes with
                                                                          | None => None
                                                                          | Some (accumulated_trading_value_value, bytes) =>
                                                                              match decode_bytes 8 bytes with
                                                                              | None => None
                                                                              | Some (settlement_date_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_1_price_value, bytes) =>
                                                                                      match decode_bytes 11 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_1_price_value, bytes) =>
                                                                                          match decode_bytes 15 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_1_remaining_quantity_value, bytes) =>
                                                                                              match decode_bytes 15 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_1_remaining_quantity_value, bytes) =>
                                                                                                  match decode_bytes 13 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_1_yield_value, bytes) =>
                                                                                                      match decode_bytes 13 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_1_yield_value, bytes) =>
                                                                                                          match decode_bytes 11 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                                                              match decode_bytes 11 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_2_remaining_quantity_value, bytes) =>
                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_2_remaining_quantity_value, bytes) =>
                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_2_yield_value, bytes) =>
                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_2_yield_value, bytes) =>
                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_3_price_value, bytes) =>
                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_3_price_value, bytes) =>
                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_level_3_yield_value, bytes) =>
                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_level_3_yield_value, bytes) =>
                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (bid_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_level_4_yield_value, bytes) =>
                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (bid_level_4_yield_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (ask_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (bid_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (ask_level_5_yield_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (bid_level_5_yield_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (bid_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; trading_date := trading_date_value; trading_value := trading_value_value; bond_yield := bond_yield_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; yield_opening_price := yield_opening_price_value; yield_todays_high := yield_todays_high_value; yield_todays_low := yield_todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; settlement_date := settlement_date_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_remaining_quantity := ask_level_1_remaining_quantity_value; bid_level_1_remaining_quantity := bid_level_1_remaining_quantity_value; ask_level_1_yield := ask_level_1_yield_value; bid_level_1_yield := bid_level_1_yield_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_remaining_quantity := ask_level_2_remaining_quantity_value; bid_level_2_remaining_quantity := bid_level_2_remaining_quantity_value; ask_level_2_yield := ask_level_2_yield_value; bid_level_2_yield := bid_level_2_yield_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_remaining_quantity := ask_level_3_remaining_quantity_value; bid_level_3_remaining_quantity := bid_level_3_remaining_quantity_value; ask_level_3_yield := ask_level_3_yield_value; bid_level_3_yield := bid_level_3_yield_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_remaining_quantity := ask_level_4_remaining_quantity_value; bid_level_4_remaining_quantity := bid_level_4_remaining_quantity_value; ask_level_4_yield := ask_level_4_yield_value; bid_level_4_yield := bid_level_4_yield_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_remaining_quantity := ask_level_5_remaining_quantity_value; bid_level_5_remaining_quantity := bid_level_5_remaining_quantity_value; ask_level_5_yield := ask_level_5_yield_value; bid_level_5_yield := bid_level_5_yield_value; ask_total_remaining_quantity := ask_total_remaining_quantity_value; bid_total_remaining_quantity := bid_total_remaining_quantity_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 638.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 bound_51]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_51.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GeneralBondsKtbOrderFilledPlusQuoteMessage.

  Module BondsNegotiatedTradeDataMessage.

    (** Bonds Negotiated Trade Data. Negotiated trades for KTB and General Bonds. *)
    Record t := {
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      accumulated_trading_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (accumulated_trading_volume record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 15 (accumulated_trading_volume record) ++
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
                  match decode_bytes 15 bytes with
                  | None => None
                  | Some (accumulated_trading_volume_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; accumulated_trading_volume := accumulated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End BondsNegotiatedTradeDataMessage.

  Module RepoNegotiatedTradeDataMessage.

    (** REPO Negotiated Trade Data. *)
    Record t := {
      isin_code : list byte;
      rfq_accumulated_trading_value : list byte;
      report_trading_total_trading_volume : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (rfq_accumulated_trading_value record) = 22 /\
      Datatypes.length (report_trading_total_trading_volume record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 22 (rfq_accumulated_trading_value record) ++
      encode_bytes 15 (report_trading_total_trading_volume record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 22 bytes with
          | None => None
          | Some (rfq_accumulated_trading_value_value, bytes) =>
              match decode_bytes 15 bytes with
              | None => None
              | Some (report_trading_total_trading_volume_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (end_keyword_value, bytes) =>
                      Some ({| isin_code := isin_code_value; rfq_accumulated_trading_value := rfq_accumulated_trading_value_value; report_trading_total_trading_volume := report_trading_total_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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

  End RepoNegotiatedTradeDataMessage.

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

  Module BabyBondsReportingMarketYieldMessage.

    (** Baby Bonds reporting market yield. Reference yields per issue. *)
    Record t := {
      message_sequence_number : list byte;
      business_date : list byte;
      baby_bonds_type_code : list byte;
      report_market_yield_rate : list byte;
      report_market_a_price_with_yield : list byte;
      closing_price_yield_rate : list byte;
      closing_price_with_yield : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (baby_bonds_type_code record) = 3 /\
      Datatypes.length (report_market_yield_rate record) = 13 /\
      Datatypes.length (report_market_a_price_with_yield record) = 11 /\
      Datatypes.length (closing_price_yield_rate record) = 13 /\
      Datatypes.length (closing_price_with_yield record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 3 (baby_bonds_type_code record) ++
      encode_bytes 13 (report_market_yield_rate record) ++
      encode_bytes 11 (report_market_a_price_with_yield record) ++
      encode_bytes 13 (closing_price_yield_rate record) ++
      encode_bytes 11 (closing_price_with_yield record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (business_date_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (baby_bonds_type_code_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (report_market_yield_rate_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (report_market_a_price_with_yield_value, bytes) =>
                          match decode_bytes 13 bytes with
                          | None => None
                          | Some (closing_price_yield_rate_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (closing_price_with_yield_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| message_sequence_number := message_sequence_number_value; business_date := business_date_value; baby_bonds_type_code := baby_bonds_type_code_value; report_market_yield_rate := report_market_yield_rate_value; report_market_a_price_with_yield := report_market_a_price_with_yield_value; closing_price_yield_rate := closing_price_yield_rate_value; closing_price_with_yield := closing_price_with_yield_value; end_keyword := end_keyword_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
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

  End BabyBondsReportingMarketYieldMessage.

  Module KtbConfirmedInfoForWitMessage.

    (** KTB Confirmed info for WIT (When-Issued Trading). *)
    Record t := {
      isin_code : list byte;
      trading_date : list byte;
      bid_closing_date : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      cancellation : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (bid_closing_date record) = 8 /\
      Datatypes.length (accumulated_trading_volume record) = 15 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (cancellation record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 8 (bid_closing_date record) ++
      encode_bytes 15 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (cancellation record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trading_date_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (bid_closing_date_value, bytes) =>
                  match decode_bytes 15 bytes with
                  | None => None
                  | Some (accumulated_trading_volume_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (accumulated_trading_value_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (cancellation_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| isin_code := isin_code_value; trading_date := trading_date_value; bid_closing_date := bid_closing_date_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; cancellation := cancellation_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
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

  End KtbConfirmedInfoForWitMessage.

  Module KtbShortTermYieldMessage.

    (** KTB Short-term Yield reference. *)
    Record t := {
      transmission_date : list byte;
      calculation_time : list byte;
      short_term_interest_rates_type_code : list byte;
      short_term_yield : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (transmission_date record) = 8 /\
      Datatypes.length (calculation_time record) = 9 /\
      Datatypes.length (short_term_interest_rates_type_code record) = 1 /\
      Datatypes.length (short_term_yield record) = 13 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (transmission_date record) ++
      encode_bytes 9 (calculation_time record) ++
      encode_bytes 1 (short_term_interest_rates_type_code record) ++
      encode_bytes 13 (short_term_yield record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (transmission_date_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (calculation_time_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (short_term_interest_rates_type_code_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (short_term_yield_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| transmission_date := transmission_date_value; calculation_time := calculation_time_value; short_term_interest_rates_type_code := short_term_interest_rates_type_code_value; short_term_yield := short_term_yield_value; end_keyword := end_keyword_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End KtbShortTermYieldMessage.

  Module KtbAverageYieldMessage.

    (** KTB Average Yield reference. *)
    Record t := {
      transmission_date : list byte;
      calculation_time : list byte;
      short_term_interest_rates_type_code : list byte;
      average_yield : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (transmission_date record) = 8 /\
      Datatypes.length (calculation_time record) = 9 /\
      Datatypes.length (short_term_interest_rates_type_code record) = 1 /\
      Datatypes.length (average_yield record) = 13 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (transmission_date record) ++
      encode_bytes 9 (calculation_time record) ++
      encode_bytes 1 (short_term_interest_rates_type_code record) ++
      encode_bytes 13 (average_yield record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (transmission_date_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (calculation_time_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (short_term_interest_rates_type_code_value, bytes) =>
                  match decode_bytes 13 bytes with
                  | None => None
                  | Some (average_yield_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| transmission_date := transmission_date_value; calculation_time := calculation_time_value; short_term_interest_rates_type_code := short_term_interest_rates_type_code_value; average_yield := average_yield_value; end_keyword := end_keyword_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End KtbAverageYieldMessage.

  Module BondsCreditRatingInformationMessage.

    (** Bonds Credit Rating Information. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      transmission_date : list byte;
      credit_rating_agency_code_no_1 : list byte;
      credit_rating_per_agency_code_no_1 : list byte;
      sf_ratings_1 : list byte;
      credit_rating_agency_code_no_2 : list byte;
      credit_rating_per_agency_code_no_2 : list byte;
      sf_ratings_2 : list byte;
      credit_rating_agency_code_no_3 : list byte;
      credit_rating_per_agency_code_no_3 : list byte;
      sf_ratings_3 : list byte;
      credit_rating_agency_code_no_4 : list byte;
      credit_rating_per_agency_code_no_4 : list byte;
      sf_ratings_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (transmission_date record) = 8 /\
      Datatypes.length (credit_rating_agency_code_no_1 record) = 4 /\
      Datatypes.length (credit_rating_per_agency_code_no_1 record) = 4 /\
      Datatypes.length (sf_ratings_1 record) = 1 /\
      Datatypes.length (credit_rating_agency_code_no_2 record) = 4 /\
      Datatypes.length (credit_rating_per_agency_code_no_2 record) = 4 /\
      Datatypes.length (sf_ratings_2 record) = 1 /\
      Datatypes.length (credit_rating_agency_code_no_3 record) = 4 /\
      Datatypes.length (credit_rating_per_agency_code_no_3 record) = 4 /\
      Datatypes.length (sf_ratings_3 record) = 1 /\
      Datatypes.length (credit_rating_agency_code_no_4 record) = 4 /\
      Datatypes.length (credit_rating_per_agency_code_no_4 record) = 4 /\
      Datatypes.length (sf_ratings_4 record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (transmission_date record) ++
      encode_bytes 4 (credit_rating_agency_code_no_1 record) ++
      encode_bytes 4 (credit_rating_per_agency_code_no_1 record) ++
      encode_bytes 1 (sf_ratings_1 record) ++
      encode_bytes 4 (credit_rating_agency_code_no_2 record) ++
      encode_bytes 4 (credit_rating_per_agency_code_no_2 record) ++
      encode_bytes 1 (sf_ratings_2 record) ++
      encode_bytes 4 (credit_rating_agency_code_no_3 record) ++
      encode_bytes 4 (credit_rating_per_agency_code_no_3 record) ++
      encode_bytes 1 (sf_ratings_3 record) ++
      encode_bytes 4 (credit_rating_agency_code_no_4 record) ++
      encode_bytes 4 (credit_rating_per_agency_code_no_4 record) ++
      encode_bytes 1 (sf_ratings_4 record) ++
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
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (credit_rating_agency_code_no_1_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (credit_rating_per_agency_code_no_1_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sf_ratings_1_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (credit_rating_agency_code_no_2_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (credit_rating_per_agency_code_no_2_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (sf_ratings_2_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (credit_rating_agency_code_no_3_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (credit_rating_per_agency_code_no_3_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (sf_ratings_3_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (credit_rating_agency_code_no_4_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (credit_rating_per_agency_code_no_4_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (sf_ratings_4_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; transmission_date := transmission_date_value; credit_rating_agency_code_no_1 := credit_rating_agency_code_no_1_value; credit_rating_per_agency_code_no_1 := credit_rating_per_agency_code_no_1_value; sf_ratings_1 := sf_ratings_1_value; credit_rating_agency_code_no_2 := credit_rating_agency_code_no_2_value; credit_rating_per_agency_code_no_2 := credit_rating_per_agency_code_no_2_value; sf_ratings_2 := sf_ratings_2_value; credit_rating_agency_code_no_3 := credit_rating_agency_code_no_3_value; credit_rating_per_agency_code_no_3 := credit_rating_per_agency_code_no_3_value; sf_ratings_3 := sf_ratings_3_value; credit_rating_agency_code_no_4 := credit_rating_agency_code_no_4_value; credit_rating_per_agency_code_no_4 := credit_rating_per_agency_code_no_4_value; sf_ratings_4 := sf_ratings_4_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
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

  End BondsCreditRatingInformationMessage.

  Module RegularBondsDisclosureBasicExchangeRateMessage.

    (** Regular Bonds Disclosure of Basic Exchange Rate for Settlement. *)
    Record t := {
      disclosing_data_type_code : list byte;
      disclosure_time : list byte;
      applied_exchange_rate : list byte;
      currency_type_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (disclosing_data_type_code record) = 3 /\
      Datatypes.length (disclosure_time record) = 9 /\
      Datatypes.length (applied_exchange_rate record) = 13 /\
      Datatypes.length (currency_type_code record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (disclosing_data_type_code record) ++
      encode_bytes 9 (disclosure_time record) ++
      encode_bytes 13 (applied_exchange_rate record) ++
      encode_bytes 1 (currency_type_code record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (disclosing_data_type_code_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (disclosure_time_value, bytes) =>
              match decode_bytes 13 bytes with
              | None => None
              | Some (applied_exchange_rate_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (currency_type_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| disclosing_data_type_code := disclosing_data_type_code_value; disclosure_time := disclosure_time_value; applied_exchange_rate := applied_exchange_rate_value; currency_type_code := currency_type_code_value; end_keyword := end_keyword_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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

  End RegularBondsDisclosureBasicExchangeRateMessage.

  Module InvestorActivitiesPerBondTypesMessage.

    (** Investor Activities per Bond Types. Aggregated bid/ask volumes and values per investor category and bond type. *)
    Record t := {
      investor_code : list byte;
      bond_category_code : list byte;
      accumulated_ask_trading_volume : list byte;
      accumulated_ask_trading_value : list byte;
      accumulated_bid_trading_volume : list byte;
      accumulated_bid_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (investor_code record) = 4 /\
      Datatypes.length (bond_category_code record) = 6 /\
      Datatypes.length (accumulated_ask_trading_volume record) = 15 /\
      Datatypes.length (accumulated_ask_trading_value record) = 22 /\
      Datatypes.length (accumulated_bid_trading_volume record) = 15 /\
      Datatypes.length (accumulated_bid_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (investor_code record) ++
      encode_bytes 6 (bond_category_code record) ++
      encode_bytes 15 (accumulated_ask_trading_volume record) ++
      encode_bytes 22 (accumulated_ask_trading_value record) ++
      encode_bytes 15 (accumulated_bid_trading_volume record) ++
      encode_bytes 22 (accumulated_bid_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (investor_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (bond_category_code_value, bytes) =>
              match decode_bytes 15 bytes with
              | None => None
              | Some (accumulated_ask_trading_volume_value, bytes) =>
                  match decode_bytes 22 bytes with
                  | None => None
                  | Some (accumulated_ask_trading_value_value, bytes) =>
                      match decode_bytes 15 bytes with
                      | None => None
                      | Some (accumulated_bid_trading_volume_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (accumulated_bid_trading_value_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| investor_code := investor_code_value; bond_category_code := bond_category_code_value; accumulated_ask_trading_volume := accumulated_ask_trading_volume_value; accumulated_ask_trading_value := accumulated_ask_trading_value_value; accumulated_bid_trading_volume := accumulated_bid_trading_volume_value; accumulated_bid_trading_value := accumulated_bid_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 85.
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

  End InvestorActivitiesPerBondTypesMessage.

  Module BondsIsinIssueInformationMessage.

    (** Bonds ISIN Issue Information (IFMSRID0038) — Bonds A. Comprehensive bond issue reference data. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      transmission_date : list byte;
      transmission_time : list byte;
      record_process_category : list byte;
      abbreviated_issue_name : list byte;
      abbreviated_issue_name_in_en : list byte;
      issuer_code : list byte;
      bond_listing_type_code : list byte;
      bond_category_code : list byte;
      bond_type_code : list byte;
      special_bond_issue_code : list byte;
      mb_type_code : list byte;
      bond_guaranteed_type_code : list byte;
      guaranteed_rate_for_payment : list byte;
      other_types_of_bond : list byte;
      option_embedded_type_code : list byte;
      coupon_payment_type_code : list byte;
      risk_bond_redemption_type_code : list byte;
      bond_issuance_type_code : list byte;
      securitization_type_code : list byte;
      redemption_priority_type_code : list byte;
      listing_date : list byte;
      issue_date : list byte;
      redemption_date : list byte;
      sale_date : list byte;
      the_1_st_coupon_payment_date : list byte;
      bond_issuance_rate : list byte;
      coupon_rate : list byte;
      monthly_cycle_of_coupon_payment : list byte;
      coupon_payment_timing_code : list byte;
      interest_payment : list byte;
      coupon_payment_date_type_code : list byte;
      decimal_point_of_coupon_type_code : list byte;
      number_of_months_to_pay_interest : list byte;
      bond_sale_type_code : list byte;
      pre_issue_sale_coupon_payment_type_code : list byte;
      issuing_amount : list byte;
      listed_amount : list byte;
      confirmation_of_lump_sum_payment : list byte;
      currency_type_code : list byte;
      redemption_ratio_at_maturity : list byte;
      yield_to_maturity : list byte;
      guaranteed_yield_effective_date : list byte;
      additional_yield : list byte;
      additional_yield_effective_date : list byte;
      facility_fund : list byte;
      maintenance_fund : list byte;
      loan_fund : list byte;
      other_funds : list byte;
      inscription_type_of_bond : list byte;
      taxation : list byte;
      bond_lead_manager_company_code : list byte;
      payment_guarantor_code : list byte;
      trustee_code : list byte;
      register_institute_code : list byte;
      payment_agent_code : list byte;
      abbreviated_issue_code : list byte;
      bond_delisting_reason_code : list byte;
      bond_delisted_date : list byte;
      equity_linked_bond_rights_type_code : list byte;
      isin : list byte;
      issue_name : list byte;
      equity_linked_bond_exercise_price : list byte;
      exercise_ratio : list byte;
      date_to_start_exercising : list byte;
      date_to_end_exercising : list byte;
      institution_code : list byte;
      record_date_of_dividend_payout : list byte;
      profit_participating_accum_status : list byte;
      issue_code_of_post_exercise : list byte;
      amortization_type_code : list byte;
      level_payment_amount : list byte;
      number_of_months_for_grace : list byte;
      interest_type_code_during_amortization : list byte;
      number_of_amortization : list byte;
      interest_rate_decision_other_base_rate_name : list byte;
      spread : list byte;
      timing_of_interest_rate_decision_type_code : list byte;
      upper_limit_coupon_rate : list byte;
      lower_limit_coupon_rate : list byte;
      the_date_to_decide_interest_rate : list byte;
      first_call_exercise_start_date : list byte;
      first_call_exercise_end_date : list byte;
      second_call_exercise_start_date : list byte;
      second_call_exercise_end_date : list byte;
      first_put_exercise_start_date : list byte;
      first_put_exercise_end_date : list byte;
      second_put_exercise_start_date : list byte;
      second_put_exercise_end_date : list byte;
      coupon_payment_decision_code_for_bank_holidays : list byte;
      hybrid_bond : list byte;
      co_cos_type_code : list byte;
      coupon_rate_confirmation : list byte;
      principal_guranteed_rate : list byte;
      participating_rate : list byte;
      maximum_yield : list byte;
      strip_bond_type_code : list byte;
      original_bond_type_code_subjec_to_strip : list byte;
      unstripped_balance : list byte;
      inflation_indexed_category : list byte;
      reference_index_for_issue_date : list byte;
      coupon_rate_decision_base_rate_type_code : list byte;
      bond_odd_lot_days_base_interest_type_code : list byte;
      base_interest_rate_on_bank_holidays_type_code : list byte;
      accrued_interest_rate_on_bank_holidays_type_code : list byte;
      principal_payment_methods_on_bank_holidays_type_code : list byte;
      principal_base_rate_on_bank_holidays_type_code : list byte;
      principal_accrued_interest_rate_on_bank_holidays_type_code : list byte;
      stop_out_rate : list byte;
      crowdfunding : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (transmission_date record) = 8 /\
      Datatypes.length (transmission_time record) = 9 /\
      Datatypes.length (record_process_category record) = 1 /\
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (abbreviated_issue_name_in_en record) = 40 /\
      Datatypes.length (issuer_code record) = 5 /\
      Datatypes.length (bond_listing_type_code record) = 1 /\
      Datatypes.length (bond_category_code record) = 6 /\
      Datatypes.length (bond_type_code record) = 2 /\
      Datatypes.length (special_bond_issue_code record) = 3 /\
      Datatypes.length (mb_type_code record) = 1 /\
      Datatypes.length (bond_guaranteed_type_code record) = 1 /\
      Datatypes.length (guaranteed_rate_for_payment record) = 13 /\
      Datatypes.length (other_types_of_bond record) = 1 /\
      Datatypes.length (option_embedded_type_code record) = 1 /\
      Datatypes.length (coupon_payment_type_code record) = 2 /\
      Datatypes.length (risk_bond_redemption_type_code record) = 1 /\
      Datatypes.length (bond_issuance_type_code record) = 3 /\
      Datatypes.length (securitization_type_code record) = 2 /\
      Datatypes.length (redemption_priority_type_code record) = 1 /\
      Datatypes.length (listing_date record) = 8 /\
      Datatypes.length (issue_date record) = 8 /\
      Datatypes.length (redemption_date record) = 8 /\
      Datatypes.length (sale_date record) = 8 /\
      Datatypes.length (the_1_st_coupon_payment_date record) = 8 /\
      Datatypes.length (bond_issuance_rate record) = 13 /\
      Datatypes.length (coupon_rate record) = 14 /\
      Datatypes.length (monthly_cycle_of_coupon_payment record) = 4 /\
      Datatypes.length (coupon_payment_timing_code record) = 1 /\
      Datatypes.length (interest_payment record) = 1 /\
      Datatypes.length (coupon_payment_date_type_code record) = 1 /\
      Datatypes.length (decimal_point_of_coupon_type_code record) = 1 /\
      Datatypes.length (number_of_months_to_pay_interest record) = 4 /\
      Datatypes.length (bond_sale_type_code record) = 1 /\
      Datatypes.length (pre_issue_sale_coupon_payment_type_code record) = 1 /\
      Datatypes.length (issuing_amount record) = 22 /\
      Datatypes.length (listed_amount record) = 22 /\
      Datatypes.length (confirmation_of_lump_sum_payment record) = 1 /\
      Datatypes.length (currency_type_code record) = 1 /\
      Datatypes.length (redemption_ratio_at_maturity record) = 13 /\
      Datatypes.length (yield_to_maturity record) = 13 /\
      Datatypes.length (guaranteed_yield_effective_date record) = 8 /\
      Datatypes.length (additional_yield record) = 13 /\
      Datatypes.length (additional_yield_effective_date record) = 8 /\
      Datatypes.length (facility_fund record) = 22 /\
      Datatypes.length (maintenance_fund record) = 22 /\
      Datatypes.length (loan_fund record) = 22 /\
      Datatypes.length (other_funds record) = 22 /\
      Datatypes.length (inscription_type_of_bond record) = 1 /\
      Datatypes.length (taxation record) = 1 /\
      Datatypes.length (bond_lead_manager_company_code record) = 4 /\
      Datatypes.length (payment_guarantor_code record) = 4 /\
      Datatypes.length (trustee_code record) = 4 /\
      Datatypes.length (register_institute_code record) = 4 /\
      Datatypes.length (payment_agent_code record) = 4 /\
      Datatypes.length (abbreviated_issue_code record) = 9 /\
      Datatypes.length (bond_delisting_reason_code record) = 2 /\
      Datatypes.length (bond_delisted_date record) = 8 /\
      Datatypes.length (equity_linked_bond_rights_type_code record) = 2 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (issue_name record) = 80 /\
      Datatypes.length (equity_linked_bond_exercise_price record) = 11 /\
      Datatypes.length (exercise_ratio record) = 7 /\
      Datatypes.length (date_to_start_exercising record) = 8 /\
      Datatypes.length (date_to_end_exercising record) = 8 /\
      Datatypes.length (institution_code record) = 4 /\
      Datatypes.length (record_date_of_dividend_payout record) = 1 /\
      Datatypes.length (profit_participating_accum_status record) = 1 /\
      Datatypes.length (issue_code_of_post_exercise record) = 12 /\
      Datatypes.length (amortization_type_code record) = 1 /\
      Datatypes.length (level_payment_amount record) = 22 /\
      Datatypes.length (number_of_months_for_grace record) = 4 /\
      Datatypes.length (interest_type_code_during_amortization record) = 1 /\
      Datatypes.length (number_of_amortization record) = 5 /\
      Datatypes.length (interest_rate_decision_other_base_rate_name record) = 20 /\
      Datatypes.length (spread record) = 10 /\
      Datatypes.length (timing_of_interest_rate_decision_type_code record) = 1 /\
      Datatypes.length (upper_limit_coupon_rate record) = 14 /\
      Datatypes.length (lower_limit_coupon_rate record) = 14 /\
      Datatypes.length (the_date_to_decide_interest_rate record) = 8 /\
      Datatypes.length (first_call_exercise_start_date record) = 8 /\
      Datatypes.length (first_call_exercise_end_date record) = 8 /\
      Datatypes.length (second_call_exercise_start_date record) = 8 /\
      Datatypes.length (second_call_exercise_end_date record) = 8 /\
      Datatypes.length (first_put_exercise_start_date record) = 8 /\
      Datatypes.length (first_put_exercise_end_date record) = 8 /\
      Datatypes.length (second_put_exercise_start_date record) = 8 /\
      Datatypes.length (second_put_exercise_end_date record) = 8 /\
      Datatypes.length (coupon_payment_decision_code_for_bank_holidays record) = 1 /\
      Datatypes.length (hybrid_bond record) = 1 /\
      Datatypes.length (co_cos_type_code record) = 1 /\
      Datatypes.length (coupon_rate_confirmation record) = 1 /\
      Datatypes.length (principal_guranteed_rate record) = 13 /\
      Datatypes.length (participating_rate record) = 11 /\
      Datatypes.length (maximum_yield record) = 11 /\
      Datatypes.length (strip_bond_type_code record) = 1 /\
      Datatypes.length (original_bond_type_code_subjec_to_strip record) = 12 /\
      Datatypes.length (unstripped_balance record) = 22 /\
      Datatypes.length (inflation_indexed_category record) = 1 /\
      Datatypes.length (reference_index_for_issue_date record) = 11 /\
      Datatypes.length (coupon_rate_decision_base_rate_type_code record) = 2 /\
      Datatypes.length (bond_odd_lot_days_base_interest_type_code record) = 1 /\
      Datatypes.length (base_interest_rate_on_bank_holidays_type_code record) = 1 /\
      Datatypes.length (accrued_interest_rate_on_bank_holidays_type_code record) = 14 /\
      Datatypes.length (principal_payment_methods_on_bank_holidays_type_code record) = 1 /\
      Datatypes.length (principal_base_rate_on_bank_holidays_type_code record) = 1 /\
      Datatypes.length (principal_accrued_interest_rate_on_bank_holidays_type_code record) = 14 /\
      Datatypes.length (stop_out_rate record) = 14 /\
      Datatypes.length (crowdfunding record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (transmission_date record) ++
      encode_bytes 9 (transmission_time record) ++
      encode_bytes 1 (record_process_category record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name_in_en record) ++
      encode_bytes 5 (issuer_code record) ++
      encode_bytes 1 (bond_listing_type_code record) ++
      encode_bytes 6 (bond_category_code record) ++
      encode_bytes 2 (bond_type_code record) ++
      encode_bytes 3 (special_bond_issue_code record) ++
      encode_bytes 1 (mb_type_code record) ++
      encode_bytes 1 (bond_guaranteed_type_code record) ++
      encode_bytes 13 (guaranteed_rate_for_payment record) ++
      encode_bytes 1 (other_types_of_bond record) ++
      encode_bytes 1 (option_embedded_type_code record) ++
      encode_bytes 2 (coupon_payment_type_code record) ++
      encode_bytes 1 (risk_bond_redemption_type_code record) ++
      encode_bytes 3 (bond_issuance_type_code record) ++
      encode_bytes 2 (securitization_type_code record) ++
      encode_bytes 1 (redemption_priority_type_code record) ++
      encode_bytes 8 (listing_date record) ++
      encode_bytes 8 (issue_date record) ++
      encode_bytes 8 (redemption_date record) ++
      encode_bytes 8 (sale_date record) ++
      encode_bytes 8 (the_1_st_coupon_payment_date record) ++
      encode_bytes 13 (bond_issuance_rate record) ++
      encode_bytes 14 (coupon_rate record) ++
      encode_bytes 4 (monthly_cycle_of_coupon_payment record) ++
      encode_bytes 1 (coupon_payment_timing_code record) ++
      encode_bytes 1 (interest_payment record) ++
      encode_bytes 1 (coupon_payment_date_type_code record) ++
      encode_bytes 1 (decimal_point_of_coupon_type_code record) ++
      encode_bytes 4 (number_of_months_to_pay_interest record) ++
      encode_bytes 1 (bond_sale_type_code record) ++
      encode_bytes 1 (pre_issue_sale_coupon_payment_type_code record) ++
      encode_bytes 22 (issuing_amount record) ++
      encode_bytes 22 (listed_amount record) ++
      encode_bytes 1 (confirmation_of_lump_sum_payment record) ++
      encode_bytes 1 (currency_type_code record) ++
      encode_bytes 13 (redemption_ratio_at_maturity record) ++
      encode_bytes 13 (yield_to_maturity record) ++
      encode_bytes 8 (guaranteed_yield_effective_date record) ++
      encode_bytes 13 (additional_yield record) ++
      encode_bytes 8 (additional_yield_effective_date record) ++
      encode_bytes 22 (facility_fund record) ++
      encode_bytes 22 (maintenance_fund record) ++
      encode_bytes 22 (loan_fund record) ++
      encode_bytes 22 (other_funds record) ++
      encode_bytes 1 (inscription_type_of_bond record) ++
      encode_bytes 1 (taxation record) ++
      encode_bytes 4 (bond_lead_manager_company_code record) ++
      encode_bytes 4 (payment_guarantor_code record) ++
      encode_bytes 4 (trustee_code record) ++
      encode_bytes 4 (register_institute_code record) ++
      encode_bytes 4 (payment_agent_code record) ++
      encode_bytes 9 (abbreviated_issue_code record) ++
      encode_bytes 2 (bond_delisting_reason_code record) ++
      encode_bytes 8 (bond_delisted_date record) ++
      encode_bytes 2 (equity_linked_bond_rights_type_code record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 80 (issue_name record) ++
      encode_bytes 11 (equity_linked_bond_exercise_price record) ++
      encode_bytes 7 (exercise_ratio record) ++
      encode_bytes 8 (date_to_start_exercising record) ++
      encode_bytes 8 (date_to_end_exercising record) ++
      encode_bytes 4 (institution_code record) ++
      encode_bytes 1 (record_date_of_dividend_payout record) ++
      encode_bytes 1 (profit_participating_accum_status record) ++
      encode_bytes 12 (issue_code_of_post_exercise record) ++
      encode_bytes 1 (amortization_type_code record) ++
      encode_bytes 22 (level_payment_amount record) ++
      encode_bytes 4 (number_of_months_for_grace record) ++
      encode_bytes 1 (interest_type_code_during_amortization record) ++
      encode_bytes 5 (number_of_amortization record) ++
      encode_bytes 20 (interest_rate_decision_other_base_rate_name record) ++
      encode_bytes 10 (spread record) ++
      encode_bytes 1 (timing_of_interest_rate_decision_type_code record) ++
      encode_bytes 14 (upper_limit_coupon_rate record) ++
      encode_bytes 14 (lower_limit_coupon_rate record) ++
      encode_bytes 8 (the_date_to_decide_interest_rate record) ++
      encode_bytes 8 (first_call_exercise_start_date record) ++
      encode_bytes 8 (first_call_exercise_end_date record) ++
      encode_bytes 8 (second_call_exercise_start_date record) ++
      encode_bytes 8 (second_call_exercise_end_date record) ++
      encode_bytes 8 (first_put_exercise_start_date record) ++
      encode_bytes 8 (first_put_exercise_end_date record) ++
      encode_bytes 8 (second_put_exercise_start_date record) ++
      encode_bytes 8 (second_put_exercise_end_date record) ++
      encode_bytes 1 (coupon_payment_decision_code_for_bank_holidays record) ++
      encode_bytes 1 (hybrid_bond record) ++
      encode_bytes 1 (co_cos_type_code record) ++
      encode_bytes 1 (coupon_rate_confirmation record) ++
      encode_bytes 13 (principal_guranteed_rate record) ++
      encode_bytes 11 (participating_rate record) ++
      encode_bytes 11 (maximum_yield record) ++
      encode_bytes 1 (strip_bond_type_code record) ++
      encode_bytes 12 (original_bond_type_code_subjec_to_strip record) ++
      encode_bytes 22 (unstripped_balance record) ++
      encode_bytes 1 (inflation_indexed_category record) ++
      encode_bytes 11 (reference_index_for_issue_date record) ++
      encode_bytes 2 (coupon_rate_decision_base_rate_type_code record) ++
      encode_bytes 1 (bond_odd_lot_days_base_interest_type_code record) ++
      encode_bytes 1 (base_interest_rate_on_bank_holidays_type_code record) ++
      encode_bytes 14 (accrued_interest_rate_on_bank_holidays_type_code record) ++
      encode_bytes 1 (principal_payment_methods_on_bank_holidays_type_code record) ++
      encode_bytes 1 (principal_base_rate_on_bank_holidays_type_code record) ++
      encode_bytes 14 (principal_accrued_interest_rate_on_bank_holidays_type_code record) ++
      encode_bytes 14 (stop_out_rate record) ++
      encode_bytes 1 (crowdfunding record) ++
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
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (transmission_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (record_process_category_value, bytes) =>
                          match decode_bytes 40 bytes with
                          | None => None
                          | Some (abbreviated_issue_name_value, bytes) =>
                              match decode_bytes 40 bytes with
                              | None => None
                              | Some (abbreviated_issue_name_in_en_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (issuer_code_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (bond_listing_type_code_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (bond_category_code_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (bond_type_code_value, bytes) =>
                                                  match decode_bytes 3 bytes with
                                                  | None => None
                                                  | Some (special_bond_issue_code_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (mb_type_code_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (bond_guaranteed_type_code_value, bytes) =>
                                                              match decode_bytes 13 bytes with
                                                              | None => None
                                                              | Some (guaranteed_rate_for_payment_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (other_types_of_bond_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (option_embedded_type_code_value, bytes) =>
                                                                          match decode_bytes 2 bytes with
                                                                          | None => None
                                                                          | Some (coupon_payment_type_code_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (risk_bond_redemption_type_code_value, bytes) =>
                                                                                  match decode_bytes 3 bytes with
                                                                                  | None => None
                                                                                  | Some (bond_issuance_type_code_value, bytes) =>
                                                                                      match decode_bytes 2 bytes with
                                                                                      | None => None
                                                                                      | Some (securitization_type_code_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (redemption_priority_type_code_value, bytes) =>
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
                                                                                                              match decode_bytes 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (the_1_st_coupon_payment_date_value, bytes) =>
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
                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (number_of_months_to_pay_interest_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bond_sale_type_code_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (pre_issue_sale_coupon_payment_type_code_value, bytes) =>
                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (issuing_amount_value, bytes) =>
                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (listed_amount_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (confirmation_of_lump_sum_payment_value, bytes) =>
                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (currency_type_code_value, bytes) =>
                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (redemption_ratio_at_maturity_value, bytes) =>
                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (yield_to_maturity_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (guaranteed_yield_effective_date_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (additional_yield_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (additional_yield_effective_date_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (facility_fund_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (maintenance_fund_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (loan_fund_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (other_funds_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (inscription_type_of_bond_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (taxation_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bond_lead_manager_company_code_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (payment_guarantor_code_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (trustee_code_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (register_institute_code_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (payment_agent_code_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (abbreviated_issue_code_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (bond_delisting_reason_code_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (bond_delisted_date_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (equity_linked_bond_rights_type_code_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (isin_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 80 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (issue_name_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (equity_linked_bond_exercise_price_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 7 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (exercise_ratio_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (date_to_start_exercising_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (date_to_end_exercising_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (institution_code_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (record_date_of_dividend_payout_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (profit_participating_accum_status_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (issue_code_of_post_exercise_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (amortization_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (level_payment_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (number_of_months_for_grace_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (interest_type_code_during_amortization_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (number_of_amortization_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (interest_rate_decision_other_base_rate_name_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 10 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (spread_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (timing_of_interest_rate_decision_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 14 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (upper_limit_coupon_rate_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 14 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (lower_limit_coupon_rate_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (the_date_to_decide_interest_rate_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (first_call_exercise_start_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (first_call_exercise_end_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (second_call_exercise_start_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (second_call_exercise_end_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (first_put_exercise_start_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (first_put_exercise_end_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                      | Some (second_put_exercise_start_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                          | Some (second_put_exercise_end_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                              | Some (coupon_payment_decision_code_for_bank_holidays_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                  | Some (hybrid_bond_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                      | Some (co_cos_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                          | Some (coupon_rate_confirmation_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                              | Some (principal_guranteed_rate_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                  | Some (participating_rate_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                      | Some (maximum_yield_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                          | Some (strip_bond_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                              | Some (original_bond_type_code_subjec_to_strip_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (unstripped_balance_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (inflation_indexed_category_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (reference_index_for_issue_date_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (coupon_rate_decision_base_rate_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (bond_odd_lot_days_base_interest_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (base_interest_rate_on_bank_holidays_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 14 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (accrued_interest_rate_on_bank_holidays_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (principal_payment_methods_on_bank_holidays_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (principal_base_rate_on_bank_holidays_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 14 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (principal_accrued_interest_rate_on_bank_holidays_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 14 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (stop_out_rate_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (crowdfunding_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; transmission_date := transmission_date_value; transmission_time := transmission_time_value; record_process_category := record_process_category_value; abbreviated_issue_name := abbreviated_issue_name_value; abbreviated_issue_name_in_en := abbreviated_issue_name_in_en_value; issuer_code := issuer_code_value; bond_listing_type_code := bond_listing_type_code_value; bond_category_code := bond_category_code_value; bond_type_code := bond_type_code_value; special_bond_issue_code := special_bond_issue_code_value; mb_type_code := mb_type_code_value; bond_guaranteed_type_code := bond_guaranteed_type_code_value; guaranteed_rate_for_payment := guaranteed_rate_for_payment_value; other_types_of_bond := other_types_of_bond_value; option_embedded_type_code := option_embedded_type_code_value; coupon_payment_type_code := coupon_payment_type_code_value; risk_bond_redemption_type_code := risk_bond_redemption_type_code_value; bond_issuance_type_code := bond_issuance_type_code_value; securitization_type_code := securitization_type_code_value; redemption_priority_type_code := redemption_priority_type_code_value; listing_date := listing_date_value; issue_date := issue_date_value; redemption_date := redemption_date_value; sale_date := sale_date_value; the_1_st_coupon_payment_date := the_1_st_coupon_payment_date_value; bond_issuance_rate := bond_issuance_rate_value; coupon_rate := coupon_rate_value; monthly_cycle_of_coupon_payment := monthly_cycle_of_coupon_payment_value; coupon_payment_timing_code := coupon_payment_timing_code_value; interest_payment := interest_payment_value; coupon_payment_date_type_code := coupon_payment_date_type_code_value; decimal_point_of_coupon_type_code := decimal_point_of_coupon_type_code_value; number_of_months_to_pay_interest := number_of_months_to_pay_interest_value; bond_sale_type_code := bond_sale_type_code_value; pre_issue_sale_coupon_payment_type_code := pre_issue_sale_coupon_payment_type_code_value; issuing_amount := issuing_amount_value; listed_amount := listed_amount_value; confirmation_of_lump_sum_payment := confirmation_of_lump_sum_payment_value; currency_type_code := currency_type_code_value; redemption_ratio_at_maturity := redemption_ratio_at_maturity_value; yield_to_maturity := yield_to_maturity_value; guaranteed_yield_effective_date := guaranteed_yield_effective_date_value; additional_yield := additional_yield_value; additional_yield_effective_date := additional_yield_effective_date_value; facility_fund := facility_fund_value; maintenance_fund := maintenance_fund_value; loan_fund := loan_fund_value; other_funds := other_funds_value; inscription_type_of_bond := inscription_type_of_bond_value; taxation := taxation_value; bond_lead_manager_company_code := bond_lead_manager_company_code_value; payment_guarantor_code := payment_guarantor_code_value; trustee_code := trustee_code_value; register_institute_code := register_institute_code_value; payment_agent_code := payment_agent_code_value; abbreviated_issue_code := abbreviated_issue_code_value; bond_delisting_reason_code := bond_delisting_reason_code_value; bond_delisted_date := bond_delisted_date_value; equity_linked_bond_rights_type_code := equity_linked_bond_rights_type_code_value; isin := isin_value; issue_name := issue_name_value; equity_linked_bond_exercise_price := equity_linked_bond_exercise_price_value; exercise_ratio := exercise_ratio_value; date_to_start_exercising := date_to_start_exercising_value; date_to_end_exercising := date_to_end_exercising_value; institution_code := institution_code_value; record_date_of_dividend_payout := record_date_of_dividend_payout_value; profit_participating_accum_status := profit_participating_accum_status_value; issue_code_of_post_exercise := issue_code_of_post_exercise_value; amortization_type_code := amortization_type_code_value; level_payment_amount := level_payment_amount_value; number_of_months_for_grace := number_of_months_for_grace_value; interest_type_code_during_amortization := interest_type_code_during_amortization_value; number_of_amortization := number_of_amortization_value; interest_rate_decision_other_base_rate_name := interest_rate_decision_other_base_rate_name_value; spread := spread_value; timing_of_interest_rate_decision_type_code := timing_of_interest_rate_decision_type_code_value; upper_limit_coupon_rate := upper_limit_coupon_rate_value; lower_limit_coupon_rate := lower_limit_coupon_rate_value; the_date_to_decide_interest_rate := the_date_to_decide_interest_rate_value; first_call_exercise_start_date := first_call_exercise_start_date_value; first_call_exercise_end_date := first_call_exercise_end_date_value; second_call_exercise_start_date := second_call_exercise_start_date_value; second_call_exercise_end_date := second_call_exercise_end_date_value; first_put_exercise_start_date := first_put_exercise_start_date_value; first_put_exercise_end_date := first_put_exercise_end_date_value; second_put_exercise_start_date := second_put_exercise_start_date_value; second_put_exercise_end_date := second_put_exercise_end_date_value; coupon_payment_decision_code_for_bank_holidays := coupon_payment_decision_code_for_bank_holidays_value; hybrid_bond := hybrid_bond_value; co_cos_type_code := co_cos_type_code_value; coupon_rate_confirmation := coupon_rate_confirmation_value; principal_guranteed_rate := principal_guranteed_rate_value; participating_rate := participating_rate_value; maximum_yield := maximum_yield_value; strip_bond_type_code := strip_bond_type_code_value; original_bond_type_code_subjec_to_strip := original_bond_type_code_subjec_to_strip_value; unstripped_balance := unstripped_balance_value; inflation_indexed_category := inflation_indexed_category_value; reference_index_for_issue_date := reference_index_for_issue_date_value; coupon_rate_decision_base_rate_type_code := coupon_rate_decision_base_rate_type_code_value; bond_odd_lot_days_base_interest_type_code := bond_odd_lot_days_base_interest_type_code_value; base_interest_rate_on_bank_holidays_type_code := base_interest_rate_on_bank_holidays_type_code_value; accrued_interest_rate_on_bank_holidays_type_code := accrued_interest_rate_on_bank_holidays_type_code_value; principal_payment_methods_on_bank_holidays_type_code := principal_payment_methods_on_bank_holidays_type_code_value; principal_base_rate_on_bank_holidays_type_code := principal_base_rate_on_bank_holidays_type_code_value; principal_accrued_interest_rate_on_bank_holidays_type_code := principal_accrued_interest_rate_on_bank_holidays_type_code_value; stop_out_rate := stop_out_rate_value; crowdfunding := crowdfunding_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 918.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 [bound_87 [bound_88 [bound_89 [bound_90 [bound_91 [bound_92 [bound_93 [bound_94 [bound_95 [bound_96 [bound_97 [bound_98 [bound_99 [bound_100 [bound_101 [bound_102 [bound_103 [bound_104 [bound_105 [bound_106 [bound_107 [bound_108 [bound_109 [bound_110 bound_111]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_107.
      rewrite decode_encode_bytes by exact bound_108.
      rewrite decode_encode_bytes by exact bound_109.
      rewrite decode_encode_bytes by exact bound_110.
      rewrite decode_encode_uint by exact bound_111.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BondsIsinIssueInformationMessage.

  Module BondsIsinInformationTextMessage.

    (** Bonds ISIN Information TEXT (IFMSRID0040) — Bonds A. Free-form text fields: issue name, conditions, ELS conditions. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      transmission_date : list byte;
      issue_name : list byte;
      english_issue_name : list byte;
      unusual_issuance_condition : list byte;
      reason_for_exercising_a_call : list byte;
      reason_for_exercising_a_put : list byte;
      contents_of_underlying_asset : list byte;
      els_condition_1 : list byte;
      els_condition_2 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (transmission_date record) = 8 /\
      Datatypes.length (issue_name record) = 80 /\
      Datatypes.length (english_issue_name record) = 80 /\
      Datatypes.length (unusual_issuance_condition record) = 60 /\
      Datatypes.length (reason_for_exercising_a_call record) = 50 /\
      Datatypes.length (reason_for_exercising_a_put record) = 50 /\
      Datatypes.length (contents_of_underlying_asset record) = 100 /\
      Datatypes.length (els_condition_1 record) = 100 /\
      Datatypes.length (els_condition_2 record) = 100 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 8 (transmission_date record) ++
      encode_bytes 80 (issue_name record) ++
      encode_bytes 80 (english_issue_name record) ++
      encode_bytes 60 (unusual_issuance_condition record) ++
      encode_bytes 50 (reason_for_exercising_a_call record) ++
      encode_bytes 50 (reason_for_exercising_a_put record) ++
      encode_bytes 100 (contents_of_underlying_asset record) ++
      encode_bytes 100 (els_condition_1 record) ++
      encode_bytes 100 (els_condition_2 record) ++
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
                  match decode_bytes 80 bytes with
                  | None => None
                  | Some (issue_name_value, bytes) =>
                      match decode_bytes 80 bytes with
                      | None => None
                      | Some (english_issue_name_value, bytes) =>
                          match decode_bytes 60 bytes with
                          | None => None
                          | Some (unusual_issuance_condition_value, bytes) =>
                              match decode_bytes 50 bytes with
                              | None => None
                              | Some (reason_for_exercising_a_call_value, bytes) =>
                                  match decode_bytes 50 bytes with
                                  | None => None
                                  | Some (reason_for_exercising_a_put_value, bytes) =>
                                      match decode_bytes 100 bytes with
                                      | None => None
                                      | Some (contents_of_underlying_asset_value, bytes) =>
                                          match decode_bytes 100 bytes with
                                          | None => None
                                          | Some (els_condition_1_value, bytes) =>
                                              match decode_bytes 100 bytes with
                                              | None => None
                                              | Some (els_condition_2_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (end_keyword_value, bytes) =>
                                                      Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; transmission_date := transmission_date_value; issue_name := issue_name_value; english_issue_name := english_issue_name_value; unusual_issuance_condition := unusual_issuance_condition_value; reason_for_exercising_a_call := reason_for_exercising_a_call_value; reason_for_exercising_a_put := reason_for_exercising_a_put_value; contents_of_underlying_asset := contents_of_underlying_asset_value; els_condition_1 := els_condition_1_value; els_condition_2 := els_condition_2_value; end_keyword := end_keyword_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 649.
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

  End BondsIsinInformationTextMessage.

  Module BabyBondsQuoteMessage.

    (** Baby Bonds Quote (IFMSRPD0024) — Bonds A SMB. 5-level depth of book with yields, per-Type breakdown. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      processing_time_of_trading_system : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_remaining_quantity : list byte;
      bid_level_1_remaining_quantity : list byte;
      ask_level_1_yield : list byte;
      bid_level_1_yield : list byte;
      ask_per_type_level_1_price : list byte;
      bid_per_type_level_1_price : list byte;
      ask_per_type_level_1_remaining_quantity : list byte;
      bid_per_type_level_1_remaining_quantity : list byte;
      ask_per_type_level_1_yield : list byte;
      bid_per_type_level_1_yield : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_remaining_quantity : list byte;
      bid_level_2_remaining_quantity : list byte;
      ask_level_2_yield : list byte;
      bid_level_2_yield : list byte;
      ask_per_type_level_2_price : list byte;
      bid_per_type_level_2_price : list byte;
      ask_per_type_level_2_remaining_quantity : list byte;
      bid_per_type_level_2_remaining_quantity : list byte;
      ask_per_type_level_2_yield : list byte;
      bid_per_type_level_2_yield : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_remaining_quantity : list byte;
      bid_level_3_remaining_quantity : list byte;
      ask_level_3_yield : list byte;
      bid_level_3_yield : list byte;
      ask_per_type_level_3_price : list byte;
      bid_per_type_level_3_price : list byte;
      ask_per_type_level_3_remaining_quantity : list byte;
      bid_per_type_level_3_remaining_quantity : list byte;
      ask_per_type_level_3_yield : list byte;
      bid_per_type_level_3_yield : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_remaining_quantity : list byte;
      bid_level_4_remaining_quantity : list byte;
      ask_level_4_yield : list byte;
      bid_level_4_yield : list byte;
      ask_per_type_level_4_price : list byte;
      bid_per_type_level_4_price : list byte;
      ask_per_type_level_4_remaining_quantity : list byte;
      bid_per_type_level_4_remaining_quantity : list byte;
      ask_per_type_level_4_yield : list byte;
      bid_per_type_level_4_yield : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_remaining_quantity : list byte;
      bid_level_5_remaining_quantity : list byte;
      ask_level_5_yield : list byte;
      bid_level_5_yield : list byte;
      ask_per_type_level_5_price : list byte;
      bid_per_type_level_5_price : list byte;
      ask_per_type_level_5_remaining_quantity : list byte;
      bid_per_type_level_5_remaining_quantity : list byte;
      ask_per_type_level_5_yield : list byte;
      bid_per_type_level_5_yield : list byte;
      ask_total_remaining_quantity : list byte;
      bid_total_remaining_quantity : list byte;
      ask_per_type_total_remaining_quantity : list byte;
      bid_per_type_total_remaining_quantity : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_1_yield record) = 13 /\
      Datatypes.length (bid_level_1_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_1_price record) = 11 /\
      Datatypes.length (bid_per_type_level_1_price record) = 11 /\
      Datatypes.length (ask_per_type_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_1_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_1_yield record) = 13 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_2_yield record) = 13 /\
      Datatypes.length (bid_level_2_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_2_price record) = 11 /\
      Datatypes.length (bid_per_type_level_2_price record) = 11 /\
      Datatypes.length (ask_per_type_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_2_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_2_yield record) = 13 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_3_yield record) = 13 /\
      Datatypes.length (bid_level_3_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_3_price record) = 11 /\
      Datatypes.length (bid_per_type_level_3_price record) = 11 /\
      Datatypes.length (ask_per_type_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_3_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_3_yield record) = 13 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_4_yield record) = 13 /\
      Datatypes.length (bid_level_4_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_4_price record) = 11 /\
      Datatypes.length (bid_per_type_level_4_price record) = 11 /\
      Datatypes.length (ask_per_type_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_4_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_4_yield record) = 13 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_5_yield record) = 13 /\
      Datatypes.length (bid_level_5_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_5_price record) = 11 /\
      Datatypes.length (bid_per_type_level_5_price record) = 11 /\
      Datatypes.length (ask_per_type_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_5_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_5_yield record) = 13 /\
      Datatypes.length (ask_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_total_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_total_remaining_quantity record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 15 (ask_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_level_1_remaining_quantity record) ++
      encode_bytes 13 (ask_level_1_yield record) ++
      encode_bytes 13 (bid_level_1_yield record) ++
      encode_bytes 11 (ask_per_type_level_1_price record) ++
      encode_bytes 11 (bid_per_type_level_1_price record) ++
      encode_bytes 15 (ask_per_type_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_1_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_1_yield record) ++
      encode_bytes 13 (bid_per_type_level_1_yield record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 15 (ask_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_level_2_remaining_quantity record) ++
      encode_bytes 13 (ask_level_2_yield record) ++
      encode_bytes 13 (bid_level_2_yield record) ++
      encode_bytes 11 (ask_per_type_level_2_price record) ++
      encode_bytes 11 (bid_per_type_level_2_price record) ++
      encode_bytes 15 (ask_per_type_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_2_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_2_yield record) ++
      encode_bytes 13 (bid_per_type_level_2_yield record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 15 (ask_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_level_3_remaining_quantity record) ++
      encode_bytes 13 (ask_level_3_yield record) ++
      encode_bytes 13 (bid_level_3_yield record) ++
      encode_bytes 11 (ask_per_type_level_3_price record) ++
      encode_bytes 11 (bid_per_type_level_3_price record) ++
      encode_bytes 15 (ask_per_type_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_3_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_3_yield record) ++
      encode_bytes 13 (bid_per_type_level_3_yield record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 15 (ask_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_level_4_remaining_quantity record) ++
      encode_bytes 13 (ask_level_4_yield record) ++
      encode_bytes 13 (bid_level_4_yield record) ++
      encode_bytes 11 (ask_per_type_level_4_price record) ++
      encode_bytes 11 (bid_per_type_level_4_price record) ++
      encode_bytes 15 (ask_per_type_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_4_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_4_yield record) ++
      encode_bytes 13 (bid_per_type_level_4_yield record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 15 (ask_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_level_5_remaining_quantity record) ++
      encode_bytes 13 (ask_level_5_yield record) ++
      encode_bytes 13 (bid_level_5_yield record) ++
      encode_bytes 11 (ask_per_type_level_5_price record) ++
      encode_bytes 11 (bid_per_type_level_5_price record) ++
      encode_bytes 15 (ask_per_type_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_5_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_5_yield record) ++
      encode_bytes 13 (bid_per_type_level_5_yield record) ++
      encode_bytes 15 (ask_total_remaining_quantity record) ++
      encode_bytes 15 (bid_total_remaining_quantity record) ++
      encode_bytes 15 (ask_per_type_total_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_total_remaining_quantity record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (ask_level_1_price_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (bid_level_1_price_value, bytes) =>
                                  match decode_bytes 15 bytes with
                                  | None => None
                                  | Some (ask_level_1_remaining_quantity_value, bytes) =>
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (bid_level_1_remaining_quantity_value, bytes) =>
                                          match decode_bytes 13 bytes with
                                          | None => None
                                          | Some (ask_level_1_yield_value, bytes) =>
                                              match decode_bytes 13 bytes with
                                              | None => None
                                              | Some (bid_level_1_yield_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (ask_per_type_level_1_price_value, bytes) =>
                                                      match decode_bytes 11 bytes with
                                                      | None => None
                                                      | Some (bid_per_type_level_1_price_value, bytes) =>
                                                          match decode_bytes 15 bytes with
                                                          | None => None
                                                          | Some (ask_per_type_level_1_remaining_quantity_value, bytes) =>
                                                              match decode_bytes 15 bytes with
                                                              | None => None
                                                              | Some (bid_per_type_level_1_remaining_quantity_value, bytes) =>
                                                                  match decode_bytes 13 bytes with
                                                                  | None => None
                                                                  | Some (ask_per_type_level_1_yield_value, bytes) =>
                                                                      match decode_bytes 13 bytes with
                                                                      | None => None
                                                                      | Some (bid_per_type_level_1_yield_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                  match decode_bytes 15 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_2_remaining_quantity_value, bytes) =>
                                                                                      match decode_bytes 15 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_2_remaining_quantity_value, bytes) =>
                                                                                          match decode_bytes 13 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_2_yield_value, bytes) =>
                                                                                              match decode_bytes 13 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_2_yield_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_per_type_level_2_price_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_per_type_level_2_price_value, bytes) =>
                                                                                                          match decode_bytes 15 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_per_type_level_2_remaining_quantity_value, bytes) =>
                                                                                                              match decode_bytes 15 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_per_type_level_2_remaining_quantity_value, bytes) =>
                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_per_type_level_2_yield_value, bytes) =>
                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_per_type_level_2_yield_value, bytes) =>
                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_3_price_value, bytes) =>
                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_3_price_value, bytes) =>
                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_3_yield_value, bytes) =>
                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_3_yield_value, bytes) =>
                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_per_type_level_3_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_per_type_level_3_price_value, bytes) =>
                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ask_per_type_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (bid_per_type_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_per_type_level_3_yield_value, bytes) =>
                                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (bid_per_type_level_3_yield_value, bytes) =>
                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (ask_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (bid_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (ask_level_4_yield_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (bid_level_4_yield_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (ask_per_type_level_4_price_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (bid_per_type_level_4_price_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_per_type_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (bid_per_type_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (ask_per_type_level_4_yield_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bid_per_type_level_4_yield_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (ask_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (bid_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (ask_level_5_yield_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (bid_level_5_yield_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (ask_per_type_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (bid_per_type_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (ask_per_type_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (bid_per_type_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (ask_per_type_level_5_yield_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (bid_per_type_level_5_yield_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (ask_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (bid_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (ask_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (bid_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_remaining_quantity := ask_level_1_remaining_quantity_value; bid_level_1_remaining_quantity := bid_level_1_remaining_quantity_value; ask_level_1_yield := ask_level_1_yield_value; bid_level_1_yield := bid_level_1_yield_value; ask_per_type_level_1_price := ask_per_type_level_1_price_value; bid_per_type_level_1_price := bid_per_type_level_1_price_value; ask_per_type_level_1_remaining_quantity := ask_per_type_level_1_remaining_quantity_value; bid_per_type_level_1_remaining_quantity := bid_per_type_level_1_remaining_quantity_value; ask_per_type_level_1_yield := ask_per_type_level_1_yield_value; bid_per_type_level_1_yield := bid_per_type_level_1_yield_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_remaining_quantity := ask_level_2_remaining_quantity_value; bid_level_2_remaining_quantity := bid_level_2_remaining_quantity_value; ask_level_2_yield := ask_level_2_yield_value; bid_level_2_yield := bid_level_2_yield_value; ask_per_type_level_2_price := ask_per_type_level_2_price_value; bid_per_type_level_2_price := bid_per_type_level_2_price_value; ask_per_type_level_2_remaining_quantity := ask_per_type_level_2_remaining_quantity_value; bid_per_type_level_2_remaining_quantity := bid_per_type_level_2_remaining_quantity_value; ask_per_type_level_2_yield := ask_per_type_level_2_yield_value; bid_per_type_level_2_yield := bid_per_type_level_2_yield_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_remaining_quantity := ask_level_3_remaining_quantity_value; bid_level_3_remaining_quantity := bid_level_3_remaining_quantity_value; ask_level_3_yield := ask_level_3_yield_value; bid_level_3_yield := bid_level_3_yield_value; ask_per_type_level_3_price := ask_per_type_level_3_price_value; bid_per_type_level_3_price := bid_per_type_level_3_price_value; ask_per_type_level_3_remaining_quantity := ask_per_type_level_3_remaining_quantity_value; bid_per_type_level_3_remaining_quantity := bid_per_type_level_3_remaining_quantity_value; ask_per_type_level_3_yield := ask_per_type_level_3_yield_value; bid_per_type_level_3_yield := bid_per_type_level_3_yield_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_remaining_quantity := ask_level_4_remaining_quantity_value; bid_level_4_remaining_quantity := bid_level_4_remaining_quantity_value; ask_level_4_yield := ask_level_4_yield_value; bid_level_4_yield := bid_level_4_yield_value; ask_per_type_level_4_price := ask_per_type_level_4_price_value; bid_per_type_level_4_price := bid_per_type_level_4_price_value; ask_per_type_level_4_remaining_quantity := ask_per_type_level_4_remaining_quantity_value; bid_per_type_level_4_remaining_quantity := bid_per_type_level_4_remaining_quantity_value; ask_per_type_level_4_yield := ask_per_type_level_4_yield_value; bid_per_type_level_4_yield := bid_per_type_level_4_yield_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_remaining_quantity := ask_level_5_remaining_quantity_value; bid_level_5_remaining_quantity := bid_level_5_remaining_quantity_value; ask_level_5_yield := ask_level_5_yield_value; bid_level_5_yield := bid_level_5_yield_value; ask_per_type_level_5_price := ask_per_type_level_5_price_value; bid_per_type_level_5_price := bid_per_type_level_5_price_value; ask_per_type_level_5_remaining_quantity := ask_per_type_level_5_remaining_quantity_value; bid_per_type_level_5_remaining_quantity := bid_per_type_level_5_remaining_quantity_value; ask_per_type_level_5_yield := ask_per_type_level_5_yield_value; bid_per_type_level_5_yield := bid_per_type_level_5_yield_value; ask_total_remaining_quantity := ask_total_remaining_quantity_value; bid_total_remaining_quantity := bid_total_remaining_quantity_value; ask_per_type_total_remaining_quantity := ask_per_type_total_remaining_quantity_value; bid_per_type_total_remaining_quantity := bid_per_type_total_remaining_quantity_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 877.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 bound_69]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_69.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BabyBondsQuoteMessage.

  Module RepoQuoteMessage.

    (** REPO Quote (IFMSRPD0025) — Bonds A RPO. 5-level depth + designated bid levels 1-10 with REPO amounts. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      processing_time_of_trading_system : list byte;
      duration_of_term_repo : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_remaining_quantity : list byte;
      bid_level_1_remaining_quantity : list byte;
      ask_level_1_trading_amount : list byte;
      total_bid_level_1_price : list byte;
      total_bid_level_1_remaining_quantity : list byte;
      bid_level_1_including_gc : list byte;
      ask_per_type_level_1_price : list byte;
      bid_per_type_level_1_price : list byte;
      ask_per_type_level_1_remaining_quantity : list byte;
      bid_per_type_level_1_remaining_quantity : list byte;
      ask_per_type_level_1_trading_amount : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_remaining_quantity : list byte;
      bid_level_2_remaining_quantity : list byte;
      ask_level_2_trading_amount : list byte;
      total_bid_level_2_price : list byte;
      total_bid_level_2_remaining_quantity : list byte;
      bid_level_2_including_gc : list byte;
      ask_per_type_level_2_price : list byte;
      bid_per_type_level_2_price : list byte;
      ask_per_type_level_2_remaining_quantity : list byte;
      bid_per_type_level_2_remaining_quantity : list byte;
      ask_per_type_level_2_trading_amount : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_remaining_quantity : list byte;
      bid_level_3_remaining_quantity : list byte;
      ask_level_3_trading_amount : list byte;
      total_bid_level_3_price : list byte;
      total_bid_level_3_remaining_quantity : list byte;
      bid_level_3_including_gc : list byte;
      ask_per_type_level_3_price : list byte;
      bid_per_type_level_3_price : list byte;
      ask_per_type_level_3_remaining_quantity : list byte;
      bid_per_type_level_3_remaining_quantity : list byte;
      ask_per_type_level_3_trading_amount : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_remaining_quantity : list byte;
      bid_level_4_remaining_quantity : list byte;
      ask_level_4_trading_amount : list byte;
      total_bid_level_4_price : list byte;
      total_bid_level_4_remaining_quantity : list byte;
      bid_level_4_including_gc : list byte;
      ask_per_type_level_4_price : list byte;
      bid_per_type_level_4_price : list byte;
      ask_per_type_level_4_remaining_quantity : list byte;
      bid_per_type_level_4_remaining_quantity : list byte;
      ask_per_type_level_4_trading_amount : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_remaining_quantity : list byte;
      bid_level_5_remaining_quantity : list byte;
      ask_level_5_trading_amount : list byte;
      total_bid_level_5_price : list byte;
      total_bid_level_5_remaining_quantity : list byte;
      bid_level_5_including_gc : list byte;
      ask_per_type_level_5_price : list byte;
      bid_per_type_level_5_price : list byte;
      ask_per_type_level_5_remaining_quantity : list byte;
      bid_per_type_level_5_remaining_quantity : list byte;
      ask_per_type_level_5_trading_amount : list byte;
      ask_total_remaining_quantity : list byte;
      bid_total_remaining_quantity : list byte;
      ask_per_type_total_remaining_quantity : list byte;
      bid_per_type_total_remaining_quantity : list byte;
      designated_bid_level_1_price : list byte;
      designated_bid_level_1_repo_remaining_quantity : list byte;
      designated_bid_level_1_isin : list byte;
      designated_bid_level_2_price : list byte;
      designated_bid_level_2_repo_remaining_quantity : list byte;
      designated_bid_level_2_isin : list byte;
      designated_bid_level_3_price : list byte;
      designated_bid_level_3_repo_remaining_quantity : list byte;
      designated_bid_level_3_isin : list byte;
      designated_bid_level_4_price : list byte;
      designated_bid_level_4_repo_remaining_quantity : list byte;
      designated_bid_level_4_isin : list byte;
      designated_bid_level_5_price : list byte;
      designated_bid_level_5_repo_remaining_quantity : list byte;
      designated_bid_level_5_isin : list byte;
      designated_bid_level_6_price : list byte;
      designated_bid_level_6_repo_remaining_quantity : list byte;
      designated_bid_level_6_isin : list byte;
      designated_bid_level_7_price : list byte;
      designated_bid_level_7_repo_remaining_quantity : list byte;
      designated_bid_level_7_isin : list byte;
      designated_bid_level_8_price : list byte;
      designated_bid_level_8_repo_remaining_quantity : list byte;
      designated_bid_level_8_isin : list byte;
      designated_bid_level_9_price : list byte;
      designated_bid_level_9_repo_remaining_quantity : list byte;
      designated_bid_level_9_isin : list byte;
      designated_bid_level_10_price : list byte;
      designated_bid_level_10_repo_remaining_quantity : list byte;
      designated_bid_level_10_isin : list byte;
      designated_best_bid_price : list byte;
      net_bid_per_type_total_remaining_quantity : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (duration_of_term_repo record) = 4 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_1_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_1_price record) = 11 /\
      Datatypes.length (total_bid_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_1_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_1_price record) = 11 /\
      Datatypes.length (bid_per_type_level_1_price record) = 11 /\
      Datatypes.length (ask_per_type_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_1_trading_amount record) = 22 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_2_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_2_price record) = 11 /\
      Datatypes.length (total_bid_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_2_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_2_price record) = 11 /\
      Datatypes.length (bid_per_type_level_2_price record) = 11 /\
      Datatypes.length (ask_per_type_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_2_trading_amount record) = 22 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_3_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_3_price record) = 11 /\
      Datatypes.length (total_bid_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_3_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_3_price record) = 11 /\
      Datatypes.length (bid_per_type_level_3_price record) = 11 /\
      Datatypes.length (ask_per_type_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_3_trading_amount record) = 22 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_4_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_4_price record) = 11 /\
      Datatypes.length (total_bid_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_4_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_4_price record) = 11 /\
      Datatypes.length (bid_per_type_level_4_price record) = 11 /\
      Datatypes.length (ask_per_type_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_4_trading_amount record) = 22 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_5_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_5_price record) = 11 /\
      Datatypes.length (total_bid_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_5_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_5_price record) = 11 /\
      Datatypes.length (bid_per_type_level_5_price record) = 11 /\
      Datatypes.length (ask_per_type_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_5_trading_amount record) = 22 /\
      Datatypes.length (ask_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_total_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_total_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_1_price record) = 11 /\
      Datatypes.length (designated_bid_level_1_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_1_isin record) = 12 /\
      Datatypes.length (designated_bid_level_2_price record) = 11 /\
      Datatypes.length (designated_bid_level_2_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_2_isin record) = 12 /\
      Datatypes.length (designated_bid_level_3_price record) = 11 /\
      Datatypes.length (designated_bid_level_3_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_3_isin record) = 12 /\
      Datatypes.length (designated_bid_level_4_price record) = 11 /\
      Datatypes.length (designated_bid_level_4_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_4_isin record) = 12 /\
      Datatypes.length (designated_bid_level_5_price record) = 11 /\
      Datatypes.length (designated_bid_level_5_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_5_isin record) = 12 /\
      Datatypes.length (designated_bid_level_6_price record) = 11 /\
      Datatypes.length (designated_bid_level_6_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_6_isin record) = 12 /\
      Datatypes.length (designated_bid_level_7_price record) = 11 /\
      Datatypes.length (designated_bid_level_7_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_7_isin record) = 12 /\
      Datatypes.length (designated_bid_level_8_price record) = 11 /\
      Datatypes.length (designated_bid_level_8_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_8_isin record) = 12 /\
      Datatypes.length (designated_bid_level_9_price record) = 11 /\
      Datatypes.length (designated_bid_level_9_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_9_isin record) = 12 /\
      Datatypes.length (designated_bid_level_10_price record) = 11 /\
      Datatypes.length (designated_bid_level_10_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_10_isin record) = 12 /\
      Datatypes.length (designated_best_bid_price record) = 11 /\
      Datatypes.length (net_bid_per_type_total_remaining_quantity record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 4 (duration_of_term_repo record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 15 (ask_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_level_1_remaining_quantity record) ++
      encode_bytes 22 (ask_level_1_trading_amount record) ++
      encode_bytes 11 (total_bid_level_1_price record) ++
      encode_bytes 15 (total_bid_level_1_remaining_quantity record) ++
      encode_bytes 1 (bid_level_1_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_1_price record) ++
      encode_bytes 11 (bid_per_type_level_1_price record) ++
      encode_bytes 15 (ask_per_type_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_1_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_1_trading_amount record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 15 (ask_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_level_2_remaining_quantity record) ++
      encode_bytes 22 (ask_level_2_trading_amount record) ++
      encode_bytes 11 (total_bid_level_2_price record) ++
      encode_bytes 15 (total_bid_level_2_remaining_quantity record) ++
      encode_bytes 1 (bid_level_2_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_2_price record) ++
      encode_bytes 11 (bid_per_type_level_2_price record) ++
      encode_bytes 15 (ask_per_type_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_2_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_2_trading_amount record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 15 (ask_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_level_3_remaining_quantity record) ++
      encode_bytes 22 (ask_level_3_trading_amount record) ++
      encode_bytes 11 (total_bid_level_3_price record) ++
      encode_bytes 15 (total_bid_level_3_remaining_quantity record) ++
      encode_bytes 1 (bid_level_3_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_3_price record) ++
      encode_bytes 11 (bid_per_type_level_3_price record) ++
      encode_bytes 15 (ask_per_type_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_3_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_3_trading_amount record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 15 (ask_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_level_4_remaining_quantity record) ++
      encode_bytes 22 (ask_level_4_trading_amount record) ++
      encode_bytes 11 (total_bid_level_4_price record) ++
      encode_bytes 15 (total_bid_level_4_remaining_quantity record) ++
      encode_bytes 1 (bid_level_4_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_4_price record) ++
      encode_bytes 11 (bid_per_type_level_4_price record) ++
      encode_bytes 15 (ask_per_type_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_4_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_4_trading_amount record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 15 (ask_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_level_5_remaining_quantity record) ++
      encode_bytes 22 (ask_level_5_trading_amount record) ++
      encode_bytes 11 (total_bid_level_5_price record) ++
      encode_bytes 15 (total_bid_level_5_remaining_quantity record) ++
      encode_bytes 1 (bid_level_5_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_5_price record) ++
      encode_bytes 11 (bid_per_type_level_5_price record) ++
      encode_bytes 15 (ask_per_type_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_5_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_5_trading_amount record) ++
      encode_bytes 15 (ask_total_remaining_quantity record) ++
      encode_bytes 15 (bid_total_remaining_quantity record) ++
      encode_bytes 15 (ask_per_type_total_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_total_remaining_quantity record) ++
      encode_bytes 11 (designated_bid_level_1_price record) ++
      encode_bytes 15 (designated_bid_level_1_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_1_isin record) ++
      encode_bytes 11 (designated_bid_level_2_price record) ++
      encode_bytes 15 (designated_bid_level_2_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_2_isin record) ++
      encode_bytes 11 (designated_bid_level_3_price record) ++
      encode_bytes 15 (designated_bid_level_3_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_3_isin record) ++
      encode_bytes 11 (designated_bid_level_4_price record) ++
      encode_bytes 15 (designated_bid_level_4_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_4_isin record) ++
      encode_bytes 11 (designated_bid_level_5_price record) ++
      encode_bytes 15 (designated_bid_level_5_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_5_isin record) ++
      encode_bytes 11 (designated_bid_level_6_price record) ++
      encode_bytes 15 (designated_bid_level_6_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_6_isin record) ++
      encode_bytes 11 (designated_bid_level_7_price record) ++
      encode_bytes 15 (designated_bid_level_7_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_7_isin record) ++
      encode_bytes 11 (designated_bid_level_8_price record) ++
      encode_bytes 15 (designated_bid_level_8_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_8_isin record) ++
      encode_bytes 11 (designated_bid_level_9_price record) ++
      encode_bytes 15 (designated_bid_level_9_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_9_isin record) ++
      encode_bytes 11 (designated_bid_level_10_price record) ++
      encode_bytes 15 (designated_bid_level_10_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_10_isin record) ++
      encode_bytes 11 (designated_best_bid_price record) ++
      encode_bytes 15 (net_bid_per_type_total_remaining_quantity record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (duration_of_term_repo_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (ask_level_1_price_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (bid_level_1_price_value, bytes) =>
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (ask_level_1_remaining_quantity_value, bytes) =>
                                          match decode_bytes 15 bytes with
                                          | None => None
                                          | Some (bid_level_1_remaining_quantity_value, bytes) =>
                                              match decode_bytes 22 bytes with
                                              | None => None
                                              | Some (ask_level_1_trading_amount_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (total_bid_level_1_price_value, bytes) =>
                                                      match decode_bytes 15 bytes with
                                                      | None => None
                                                      | Some (total_bid_level_1_remaining_quantity_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (bid_level_1_including_gc_value, bytes) =>
                                                              match decode_bytes 11 bytes with
                                                              | None => None
                                                              | Some (ask_per_type_level_1_price_value, bytes) =>
                                                                  match decode_bytes 11 bytes with
                                                                  | None => None
                                                                  | Some (bid_per_type_level_1_price_value, bytes) =>
                                                                      match decode_bytes 15 bytes with
                                                                      | None => None
                                                                      | Some (ask_per_type_level_1_remaining_quantity_value, bytes) =>
                                                                          match decode_bytes 15 bytes with
                                                                          | None => None
                                                                          | Some (bid_per_type_level_1_remaining_quantity_value, bytes) =>
                                                                              match decode_bytes 22 bytes with
                                                                              | None => None
                                                                              | Some (ask_per_type_level_1_trading_amount_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_2_price_value, bytes) =>
                                                                                      match decode_bytes 11 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_2_price_value, bytes) =>
                                                                                          match decode_bytes 15 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_2_remaining_quantity_value, bytes) =>
                                                                                              match decode_bytes 15 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_2_remaining_quantity_value, bytes) =>
                                                                                                  match decode_bytes 22 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_2_trading_amount_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (total_bid_level_2_price_value, bytes) =>
                                                                                                          match decode_bytes 15 bytes with
                                                                                                          | None => None
                                                                                                          | Some (total_bid_level_2_remaining_quantity_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_2_including_gc_value, bytes) =>
                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_per_type_level_2_price_value, bytes) =>
                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_per_type_level_2_price_value, bytes) =>
                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_per_type_level_2_remaining_quantity_value, bytes) =>
                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_per_type_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_per_type_level_2_trading_amount_value, bytes) =>
                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_level_3_price_value, bytes) =>
                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (bid_level_3_price_value, bytes) =>
                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_level_3_trading_amount_value, bytes) =>
                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (total_bid_level_3_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (total_bid_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (bid_level_3_including_gc_value, bytes) =>
                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_per_type_level_3_price_value, bytes) =>
                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (bid_per_type_level_3_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (ask_per_type_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (bid_per_type_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (ask_per_type_level_3_trading_amount_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (ask_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (bid_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_level_4_trading_amount_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (total_bid_level_4_price_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (total_bid_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bid_level_4_including_gc_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (ask_per_type_level_4_price_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (bid_per_type_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (ask_per_type_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (bid_per_type_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (ask_per_type_level_4_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (ask_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (bid_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (ask_level_5_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (total_bid_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (total_bid_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (bid_level_5_including_gc_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (ask_per_type_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (bid_per_type_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (ask_per_type_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (bid_per_type_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (ask_per_type_level_5_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (ask_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (bid_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (ask_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (bid_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_1_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_1_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_1_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_2_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_2_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_2_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_3_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_3_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_3_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_4_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_4_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_5_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_5_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_6_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_6_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_6_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_7_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_7_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_7_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_8_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_8_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_9_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_9_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_10_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_10_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_best_bid_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (net_bid_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; processing_time_of_trading_system := processing_time_of_trading_system_value; duration_of_term_repo := duration_of_term_repo_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_remaining_quantity := ask_level_1_remaining_quantity_value; bid_level_1_remaining_quantity := bid_level_1_remaining_quantity_value; ask_level_1_trading_amount := ask_level_1_trading_amount_value; total_bid_level_1_price := total_bid_level_1_price_value; total_bid_level_1_remaining_quantity := total_bid_level_1_remaining_quantity_value; bid_level_1_including_gc := bid_level_1_including_gc_value; ask_per_type_level_1_price := ask_per_type_level_1_price_value; bid_per_type_level_1_price := bid_per_type_level_1_price_value; ask_per_type_level_1_remaining_quantity := ask_per_type_level_1_remaining_quantity_value; bid_per_type_level_1_remaining_quantity := bid_per_type_level_1_remaining_quantity_value; ask_per_type_level_1_trading_amount := ask_per_type_level_1_trading_amount_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_remaining_quantity := ask_level_2_remaining_quantity_value; bid_level_2_remaining_quantity := bid_level_2_remaining_quantity_value; ask_level_2_trading_amount := ask_level_2_trading_amount_value; total_bid_level_2_price := total_bid_level_2_price_value; total_bid_level_2_remaining_quantity := total_bid_level_2_remaining_quantity_value; bid_level_2_including_gc := bid_level_2_including_gc_value; ask_per_type_level_2_price := ask_per_type_level_2_price_value; bid_per_type_level_2_price := bid_per_type_level_2_price_value; ask_per_type_level_2_remaining_quantity := ask_per_type_level_2_remaining_quantity_value; bid_per_type_level_2_remaining_quantity := bid_per_type_level_2_remaining_quantity_value; ask_per_type_level_2_trading_amount := ask_per_type_level_2_trading_amount_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_remaining_quantity := ask_level_3_remaining_quantity_value; bid_level_3_remaining_quantity := bid_level_3_remaining_quantity_value; ask_level_3_trading_amount := ask_level_3_trading_amount_value; total_bid_level_3_price := total_bid_level_3_price_value; total_bid_level_3_remaining_quantity := total_bid_level_3_remaining_quantity_value; bid_level_3_including_gc := bid_level_3_including_gc_value; ask_per_type_level_3_price := ask_per_type_level_3_price_value; bid_per_type_level_3_price := bid_per_type_level_3_price_value; ask_per_type_level_3_remaining_quantity := ask_per_type_level_3_remaining_quantity_value; bid_per_type_level_3_remaining_quantity := bid_per_type_level_3_remaining_quantity_value; ask_per_type_level_3_trading_amount := ask_per_type_level_3_trading_amount_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_remaining_quantity := ask_level_4_remaining_quantity_value; bid_level_4_remaining_quantity := bid_level_4_remaining_quantity_value; ask_level_4_trading_amount := ask_level_4_trading_amount_value; total_bid_level_4_price := total_bid_level_4_price_value; total_bid_level_4_remaining_quantity := total_bid_level_4_remaining_quantity_value; bid_level_4_including_gc := bid_level_4_including_gc_value; ask_per_type_level_4_price := ask_per_type_level_4_price_value; bid_per_type_level_4_price := bid_per_type_level_4_price_value; ask_per_type_level_4_remaining_quantity := ask_per_type_level_4_remaining_quantity_value; bid_per_type_level_4_remaining_quantity := bid_per_type_level_4_remaining_quantity_value; ask_per_type_level_4_trading_amount := ask_per_type_level_4_trading_amount_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_remaining_quantity := ask_level_5_remaining_quantity_value; bid_level_5_remaining_quantity := bid_level_5_remaining_quantity_value; ask_level_5_trading_amount := ask_level_5_trading_amount_value; total_bid_level_5_price := total_bid_level_5_price_value; total_bid_level_5_remaining_quantity := total_bid_level_5_remaining_quantity_value; bid_level_5_including_gc := bid_level_5_including_gc_value; ask_per_type_level_5_price := ask_per_type_level_5_price_value; bid_per_type_level_5_price := bid_per_type_level_5_price_value; ask_per_type_level_5_remaining_quantity := ask_per_type_level_5_remaining_quantity_value; bid_per_type_level_5_remaining_quantity := bid_per_type_level_5_remaining_quantity_value; ask_per_type_level_5_trading_amount := ask_per_type_level_5_trading_amount_value; ask_total_remaining_quantity := ask_total_remaining_quantity_value; bid_total_remaining_quantity := bid_total_remaining_quantity_value; ask_per_type_total_remaining_quantity := ask_per_type_total_remaining_quantity_value; bid_per_type_total_remaining_quantity := bid_per_type_total_remaining_quantity_value; designated_bid_level_1_price := designated_bid_level_1_price_value; designated_bid_level_1_repo_remaining_quantity := designated_bid_level_1_repo_remaining_quantity_value; designated_bid_level_1_isin := designated_bid_level_1_isin_value; designated_bid_level_2_price := designated_bid_level_2_price_value; designated_bid_level_2_repo_remaining_quantity := designated_bid_level_2_repo_remaining_quantity_value; designated_bid_level_2_isin := designated_bid_level_2_isin_value; designated_bid_level_3_price := designated_bid_level_3_price_value; designated_bid_level_3_repo_remaining_quantity := designated_bid_level_3_repo_remaining_quantity_value; designated_bid_level_3_isin := designated_bid_level_3_isin_value; designated_bid_level_4_price := designated_bid_level_4_price_value; designated_bid_level_4_repo_remaining_quantity := designated_bid_level_4_repo_remaining_quantity_value; designated_bid_level_4_isin := designated_bid_level_4_isin_value; designated_bid_level_5_price := designated_bid_level_5_price_value; designated_bid_level_5_repo_remaining_quantity := designated_bid_level_5_repo_remaining_quantity_value; designated_bid_level_5_isin := designated_bid_level_5_isin_value; designated_bid_level_6_price := designated_bid_level_6_price_value; designated_bid_level_6_repo_remaining_quantity := designated_bid_level_6_repo_remaining_quantity_value; designated_bid_level_6_isin := designated_bid_level_6_isin_value; designated_bid_level_7_price := designated_bid_level_7_price_value; designated_bid_level_7_repo_remaining_quantity := designated_bid_level_7_repo_remaining_quantity_value; designated_bid_level_7_isin := designated_bid_level_7_isin_value; designated_bid_level_8_price := designated_bid_level_8_price_value; designated_bid_level_8_repo_remaining_quantity := designated_bid_level_8_repo_remaining_quantity_value; designated_bid_level_8_isin := designated_bid_level_8_isin_value; designated_bid_level_9_price := designated_bid_level_9_price_value; designated_bid_level_9_repo_remaining_quantity := designated_bid_level_9_repo_remaining_quantity_value; designated_bid_level_9_isin := designated_bid_level_9_isin_value; designated_bid_level_10_price := designated_bid_level_10_price_value; designated_bid_level_10_repo_remaining_quantity := designated_bid_level_10_repo_remaining_quantity_value; designated_bid_level_10_isin := designated_bid_level_10_isin_value; designated_best_bid_price := designated_best_bid_price_value; net_bid_per_type_total_remaining_quantity := net_bid_per_type_total_remaining_quantity_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1382.
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

  End RepoQuoteMessage.

  Module BondsTotalRemainingVolumeOnQuotesMessage.

    (** General Bonds / Baby Bonds Total Remaining Volume on Quotes (IFMSRPD0026) — Bonds A BND (Regular Bonds). *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      ask_total_remaining_quantity : list byte;
      bid_total_remaining_quantity : list byte;
      ask_per_type_total_remaining_quantity : list byte;
      bid_per_type_total_remaining_quantity : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (ask_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_total_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_total_remaining_quantity record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 15 (ask_total_remaining_quantity record) ++
      encode_bytes 15 (bid_total_remaining_quantity record) ++
      encode_bytes 15 (ask_per_type_total_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_total_remaining_quantity record) ++
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
                          match decode_bytes 15 bytes with
                          | None => None
                          | Some (ask_total_remaining_quantity_value, bytes) =>
                              match decode_bytes 15 bytes with
                              | None => None
                              | Some (bid_total_remaining_quantity_value, bytes) =>
                                  match decode_bytes 15 bytes with
                                  | None => None
                                  | Some (ask_per_type_total_remaining_quantity_value, bytes) =>
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (bid_per_type_total_remaining_quantity_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_total_remaining_quantity := ask_total_remaining_quantity_value; bid_total_remaining_quantity := bid_total_remaining_quantity_value; ask_per_type_total_remaining_quantity := ask_per_type_total_remaining_quantity_value; bid_per_type_total_remaining_quantity := bid_per_type_total_remaining_quantity_value; end_keyword := end_keyword_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
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

  End BondsTotalRemainingVolumeOnQuotesMessage.

  Module BabyBondsOrderFilledPlusQuoteMessage.

    (** Baby Bonds Order Filled + Quote (IFMSRPD0030) — Bonds A SMB. Trade + 5-level quote with yields. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      trading_date : list byte;
      trading_value : list byte;
      bond_yield : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      yield_opening_price : list byte;
      yield_todays_high : list byte;
      yield_todays_low : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      settlement_date : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_remaining_quantity : list byte;
      bid_level_1_remaining_quantity : list byte;
      ask_level_1_yield : list byte;
      bid_level_1_yield : list byte;
      ask_per_type_level_1_price : list byte;
      bid_per_type_level_1_price : list byte;
      ask_per_type_level_1_remaining_quantity : list byte;
      bid_per_type_level_1_remaining_quantity : list byte;
      ask_per_type_level_1_yield : list byte;
      bid_per_type_level_1_yield : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_remaining_quantity : list byte;
      bid_level_2_remaining_quantity : list byte;
      ask_level_2_yield : list byte;
      bid_level_2_yield : list byte;
      ask_per_type_level_2_price : list byte;
      bid_per_type_level_2_price : list byte;
      ask_per_type_level_2_remaining_quantity : list byte;
      bid_per_type_level_2_remaining_quantity : list byte;
      ask_per_type_level_2_yield : list byte;
      bid_per_type_level_2_yield : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_remaining_quantity : list byte;
      bid_level_3_remaining_quantity : list byte;
      ask_level_3_yield : list byte;
      bid_level_3_yield : list byte;
      ask_per_type_level_3_price : list byte;
      bid_per_type_level_3_price : list byte;
      ask_per_type_level_3_remaining_quantity : list byte;
      bid_per_type_level_3_remaining_quantity : list byte;
      ask_per_type_level_3_yield : list byte;
      bid_per_type_level_3_yield : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_remaining_quantity : list byte;
      bid_level_4_remaining_quantity : list byte;
      ask_level_4_yield : list byte;
      bid_level_4_yield : list byte;
      ask_per_type_level_4_price : list byte;
      bid_per_type_level_4_price : list byte;
      ask_per_type_level_4_remaining_quantity : list byte;
      bid_per_type_level_4_remaining_quantity : list byte;
      ask_per_type_level_4_yield : list byte;
      bid_per_type_level_4_yield : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_remaining_quantity : list byte;
      bid_level_5_remaining_quantity : list byte;
      ask_level_5_yield : list byte;
      bid_level_5_yield : list byte;
      ask_per_type_level_5_price : list byte;
      bid_per_type_level_5_price : list byte;
      ask_per_type_level_5_remaining_quantity : list byte;
      bid_per_type_level_5_remaining_quantity : list byte;
      ask_per_type_level_5_yield : list byte;
      bid_per_type_level_5_yield : list byte;
      ask_total_remaining_quantity : list byte;
      bid_total_remaining_quantity : list byte;
      ask_per_type_total_remaining_quantity : list byte;
      bid_per_type_total_remaining_quantity : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (trading_value record) = 22 /\
      Datatypes.length (bond_yield record) = 13 /\
      Datatypes.length (opening_price record) = 11 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (yield_opening_price record) = 13 /\
      Datatypes.length (yield_todays_high record) = 13 /\
      Datatypes.length (yield_todays_low record) = 13 /\
      Datatypes.length (accumulated_trading_volume record) = 15 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (settlement_date record) = 8 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_1_yield record) = 13 /\
      Datatypes.length (bid_level_1_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_1_price record) = 11 /\
      Datatypes.length (bid_per_type_level_1_price record) = 11 /\
      Datatypes.length (ask_per_type_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_1_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_1_yield record) = 13 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_2_yield record) = 13 /\
      Datatypes.length (bid_level_2_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_2_price record) = 11 /\
      Datatypes.length (bid_per_type_level_2_price record) = 11 /\
      Datatypes.length (ask_per_type_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_2_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_2_yield record) = 13 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_3_yield record) = 13 /\
      Datatypes.length (bid_level_3_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_3_price record) = 11 /\
      Datatypes.length (bid_per_type_level_3_price record) = 11 /\
      Datatypes.length (ask_per_type_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_3_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_3_yield record) = 13 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_4_yield record) = 13 /\
      Datatypes.length (bid_level_4_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_4_price record) = 11 /\
      Datatypes.length (bid_per_type_level_4_price record) = 11 /\
      Datatypes.length (ask_per_type_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_4_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_4_yield record) = 13 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_5_yield record) = 13 /\
      Datatypes.length (bid_level_5_yield record) = 13 /\
      Datatypes.length (ask_per_type_level_5_price record) = 11 /\
      Datatypes.length (bid_per_type_level_5_price record) = 11 /\
      Datatypes.length (ask_per_type_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_5_yield record) = 13 /\
      Datatypes.length (bid_per_type_level_5_yield record) = 13 /\
      Datatypes.length (ask_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_total_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_total_remaining_quantity record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 22 (trading_value record) ++
      encode_bytes 13 (bond_yield record) ++
      encode_bytes 11 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 13 (yield_opening_price record) ++
      encode_bytes 13 (yield_todays_high record) ++
      encode_bytes 13 (yield_todays_low record) ++
      encode_bytes 15 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 8 (settlement_date record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 15 (ask_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_level_1_remaining_quantity record) ++
      encode_bytes 13 (ask_level_1_yield record) ++
      encode_bytes 13 (bid_level_1_yield record) ++
      encode_bytes 11 (ask_per_type_level_1_price record) ++
      encode_bytes 11 (bid_per_type_level_1_price record) ++
      encode_bytes 15 (ask_per_type_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_1_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_1_yield record) ++
      encode_bytes 13 (bid_per_type_level_1_yield record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 15 (ask_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_level_2_remaining_quantity record) ++
      encode_bytes 13 (ask_level_2_yield record) ++
      encode_bytes 13 (bid_level_2_yield record) ++
      encode_bytes 11 (ask_per_type_level_2_price record) ++
      encode_bytes 11 (bid_per_type_level_2_price record) ++
      encode_bytes 15 (ask_per_type_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_2_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_2_yield record) ++
      encode_bytes 13 (bid_per_type_level_2_yield record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 15 (ask_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_level_3_remaining_quantity record) ++
      encode_bytes 13 (ask_level_3_yield record) ++
      encode_bytes 13 (bid_level_3_yield record) ++
      encode_bytes 11 (ask_per_type_level_3_price record) ++
      encode_bytes 11 (bid_per_type_level_3_price record) ++
      encode_bytes 15 (ask_per_type_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_3_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_3_yield record) ++
      encode_bytes 13 (bid_per_type_level_3_yield record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 15 (ask_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_level_4_remaining_quantity record) ++
      encode_bytes 13 (ask_level_4_yield record) ++
      encode_bytes 13 (bid_level_4_yield record) ++
      encode_bytes 11 (ask_per_type_level_4_price record) ++
      encode_bytes 11 (bid_per_type_level_4_price record) ++
      encode_bytes 15 (ask_per_type_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_4_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_4_yield record) ++
      encode_bytes 13 (bid_per_type_level_4_yield record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 15 (ask_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_level_5_remaining_quantity record) ++
      encode_bytes 13 (ask_level_5_yield record) ++
      encode_bytes 13 (bid_level_5_yield record) ++
      encode_bytes 11 (ask_per_type_level_5_price record) ++
      encode_bytes 11 (bid_per_type_level_5_price record) ++
      encode_bytes 15 (ask_per_type_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_5_remaining_quantity record) ++
      encode_bytes 13 (ask_per_type_level_5_yield record) ++
      encode_bytes 13 (bid_per_type_level_5_yield record) ++
      encode_bytes 15 (ask_total_remaining_quantity record) ++
      encode_bytes 15 (bid_total_remaining_quantity record) ++
      encode_bytes 15 (ask_per_type_total_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_total_remaining_quantity record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (trading_price_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (trading_volume_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (trading_date_value, bytes) =>
                                      match decode_bytes 22 bytes with
                                      | None => None
                                      | Some (trading_value_value, bytes) =>
                                          match decode_bytes 13 bytes with
                                          | None => None
                                          | Some (bond_yield_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (opening_price_value, bytes) =>
                                                  match decode_bytes 11 bytes with
                                                  | None => None
                                                  | Some (todays_high_value, bytes) =>
                                                      match decode_bytes 11 bytes with
                                                      | None => None
                                                      | Some (todays_low_value, bytes) =>
                                                          match decode_bytes 13 bytes with
                                                          | None => None
                                                          | Some (yield_opening_price_value, bytes) =>
                                                              match decode_bytes 13 bytes with
                                                              | None => None
                                                              | Some (yield_todays_high_value, bytes) =>
                                                                  match decode_bytes 13 bytes with
                                                                  | None => None
                                                                  | Some (yield_todays_low_value, bytes) =>
                                                                      match decode_bytes 15 bytes with
                                                                      | None => None
                                                                      | Some (accumulated_trading_volume_value, bytes) =>
                                                                          match decode_bytes 22 bytes with
                                                                          | None => None
                                                                          | Some (accumulated_trading_value_value, bytes) =>
                                                                              match decode_bytes 8 bytes with
                                                                              | None => None
                                                                              | Some (settlement_date_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_1_price_value, bytes) =>
                                                                                      match decode_bytes 11 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_1_price_value, bytes) =>
                                                                                          match decode_bytes 15 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_1_remaining_quantity_value, bytes) =>
                                                                                              match decode_bytes 15 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_1_remaining_quantity_value, bytes) =>
                                                                                                  match decode_bytes 13 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_1_yield_value, bytes) =>
                                                                                                      match decode_bytes 13 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_1_yield_value, bytes) =>
                                                                                                          match decode_bytes 11 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_per_type_level_1_price_value, bytes) =>
                                                                                                              match decode_bytes 11 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_per_type_level_1_price_value, bytes) =>
                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_per_type_level_1_remaining_quantity_value, bytes) =>
                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_per_type_level_1_remaining_quantity_value, bytes) =>
                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_per_type_level_1_yield_value, bytes) =>
                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_per_type_level_1_yield_value, bytes) =>
                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_2_price_value, bytes) =>
                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_2_price_value, bytes) =>
                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_level_2_yield_value, bytes) =>
                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_level_2_yield_value, bytes) =>
                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ask_per_type_level_2_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (bid_per_type_level_2_price_value, bytes) =>
                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_per_type_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (bid_per_type_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_per_type_level_2_yield_value, bytes) =>
                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (bid_per_type_level_2_yield_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (ask_level_3_price_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (bid_level_3_price_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (ask_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (bid_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (ask_level_3_yield_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (bid_level_3_yield_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_per_type_level_3_price_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (bid_per_type_level_3_price_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (ask_per_type_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bid_per_type_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (ask_per_type_level_3_yield_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (bid_per_type_level_3_yield_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (ask_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (bid_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (ask_level_4_yield_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (bid_level_4_yield_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (ask_per_type_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (bid_per_type_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (ask_per_type_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (bid_per_type_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (ask_per_type_level_4_yield_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (bid_per_type_level_4_yield_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (ask_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (bid_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (ask_level_5_yield_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (bid_level_5_yield_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (ask_per_type_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (bid_per_type_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (ask_per_type_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (bid_per_type_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (ask_per_type_level_5_yield_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (bid_per_type_level_5_yield_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (ask_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (bid_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (ask_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (bid_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; trading_date := trading_date_value; trading_value := trading_value_value; bond_yield := bond_yield_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; yield_opening_price := yield_opening_price_value; yield_todays_high := yield_todays_high_value; yield_todays_low := yield_todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; settlement_date := settlement_date_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_remaining_quantity := ask_level_1_remaining_quantity_value; bid_level_1_remaining_quantity := bid_level_1_remaining_quantity_value; ask_level_1_yield := ask_level_1_yield_value; bid_level_1_yield := bid_level_1_yield_value; ask_per_type_level_1_price := ask_per_type_level_1_price_value; bid_per_type_level_1_price := bid_per_type_level_1_price_value; ask_per_type_level_1_remaining_quantity := ask_per_type_level_1_remaining_quantity_value; bid_per_type_level_1_remaining_quantity := bid_per_type_level_1_remaining_quantity_value; ask_per_type_level_1_yield := ask_per_type_level_1_yield_value; bid_per_type_level_1_yield := bid_per_type_level_1_yield_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_remaining_quantity := ask_level_2_remaining_quantity_value; bid_level_2_remaining_quantity := bid_level_2_remaining_quantity_value; ask_level_2_yield := ask_level_2_yield_value; bid_level_2_yield := bid_level_2_yield_value; ask_per_type_level_2_price := ask_per_type_level_2_price_value; bid_per_type_level_2_price := bid_per_type_level_2_price_value; ask_per_type_level_2_remaining_quantity := ask_per_type_level_2_remaining_quantity_value; bid_per_type_level_2_remaining_quantity := bid_per_type_level_2_remaining_quantity_value; ask_per_type_level_2_yield := ask_per_type_level_2_yield_value; bid_per_type_level_2_yield := bid_per_type_level_2_yield_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_remaining_quantity := ask_level_3_remaining_quantity_value; bid_level_3_remaining_quantity := bid_level_3_remaining_quantity_value; ask_level_3_yield := ask_level_3_yield_value; bid_level_3_yield := bid_level_3_yield_value; ask_per_type_level_3_price := ask_per_type_level_3_price_value; bid_per_type_level_3_price := bid_per_type_level_3_price_value; ask_per_type_level_3_remaining_quantity := ask_per_type_level_3_remaining_quantity_value; bid_per_type_level_3_remaining_quantity := bid_per_type_level_3_remaining_quantity_value; ask_per_type_level_3_yield := ask_per_type_level_3_yield_value; bid_per_type_level_3_yield := bid_per_type_level_3_yield_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_remaining_quantity := ask_level_4_remaining_quantity_value; bid_level_4_remaining_quantity := bid_level_4_remaining_quantity_value; ask_level_4_yield := ask_level_4_yield_value; bid_level_4_yield := bid_level_4_yield_value; ask_per_type_level_4_price := ask_per_type_level_4_price_value; bid_per_type_level_4_price := bid_per_type_level_4_price_value; ask_per_type_level_4_remaining_quantity := ask_per_type_level_4_remaining_quantity_value; bid_per_type_level_4_remaining_quantity := bid_per_type_level_4_remaining_quantity_value; ask_per_type_level_4_yield := ask_per_type_level_4_yield_value; bid_per_type_level_4_yield := bid_per_type_level_4_yield_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_remaining_quantity := ask_level_5_remaining_quantity_value; bid_level_5_remaining_quantity := bid_level_5_remaining_quantity_value; ask_level_5_yield := ask_level_5_yield_value; bid_level_5_yield := bid_level_5_yield_value; ask_per_type_level_5_price := ask_per_type_level_5_price_value; bid_per_type_level_5_price := bid_per_type_level_5_price_value; ask_per_type_level_5_remaining_quantity := ask_per_type_level_5_remaining_quantity_value; bid_per_type_level_5_remaining_quantity := bid_per_type_level_5_remaining_quantity_value; ask_per_type_level_5_yield := ask_per_type_level_5_yield_value; bid_per_type_level_5_yield := bid_per_type_level_5_yield_value; ask_total_remaining_quantity := ask_total_remaining_quantity_value; bid_total_remaining_quantity := bid_total_remaining_quantity_value; ask_per_type_total_remaining_quantity := ask_per_type_total_remaining_quantity_value; bid_per_type_total_remaining_quantity := bid_per_type_total_remaining_quantity_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1058.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 bound_83]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_83.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BabyBondsOrderFilledPlusQuoteMessage.

  Module RepoOrderFilledPlusQuoteMessage.

    (** REPO Order Filled + Quote (IFMSRPD0031) — Bonds A RPO. Trade + 5-level quote + designated bid levels 1-10. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      trading_date : list byte;
      trading_value : list byte;
      ask_repo_type_code : list byte;
      ask_duration_of_term_repo : list byte;
      bid_repo_type_code : list byte;
      bid_duration_of_term_repo : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      category_opening_price : list byte;
      category_todays_high : list byte;
      category_todays_low : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      category_accumulated_trading_volume : list byte;
      category_accumulated_trading_value : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_remaining_quantity : list byte;
      bid_level_1_remaining_quantity : list byte;
      ask_level_1_trading_amount : list byte;
      total_bid_level_1_price : list byte;
      total_bid_level_1_remaining_quantity : list byte;
      bid_level_1_including_gc : list byte;
      ask_per_type_level_1_price : list byte;
      bid_per_type_level_1_price : list byte;
      ask_per_type_level_1_remaining_quantity : list byte;
      bid_per_type_level_1_remaining_quantity : list byte;
      ask_per_type_level_1_trading_amount : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_remaining_quantity : list byte;
      bid_level_2_remaining_quantity : list byte;
      ask_level_2_trading_amount : list byte;
      total_bid_level_2_price : list byte;
      total_bid_level_2_remaining_quantity : list byte;
      bid_level_2_including_gc : list byte;
      ask_per_type_level_2_price : list byte;
      bid_per_type_level_2_price : list byte;
      ask_per_type_level_2_remaining_quantity : list byte;
      bid_per_type_level_2_remaining_quantity : list byte;
      ask_per_type_level_2_trading_amount : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_remaining_quantity : list byte;
      bid_level_3_remaining_quantity : list byte;
      ask_level_3_trading_amount : list byte;
      total_bid_level_3_price : list byte;
      total_bid_level_3_remaining_quantity : list byte;
      bid_level_3_including_gc : list byte;
      ask_per_type_level_3_price : list byte;
      bid_per_type_level_3_price : list byte;
      ask_per_type_level_3_remaining_quantity : list byte;
      bid_per_type_level_3_remaining_quantity : list byte;
      ask_per_type_level_3_trading_amount : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_remaining_quantity : list byte;
      bid_level_4_remaining_quantity : list byte;
      ask_level_4_trading_amount : list byte;
      total_bid_level_4_price : list byte;
      total_bid_level_4_remaining_quantity : list byte;
      bid_level_4_including_gc : list byte;
      ask_per_type_level_4_price : list byte;
      bid_per_type_level_4_price : list byte;
      ask_per_type_level_4_remaining_quantity : list byte;
      bid_per_type_level_4_remaining_quantity : list byte;
      ask_per_type_level_4_trading_amount : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_remaining_quantity : list byte;
      bid_level_5_remaining_quantity : list byte;
      ask_level_5_trading_amount : list byte;
      total_bid_level_5_price : list byte;
      total_bid_level_5_remaining_quantity : list byte;
      bid_level_5_including_gc : list byte;
      ask_per_type_level_5_price : list byte;
      bid_per_type_level_5_price : list byte;
      ask_per_type_level_5_remaining_quantity : list byte;
      bid_per_type_level_5_remaining_quantity : list byte;
      ask_per_type_level_5_trading_amount : list byte;
      ask_total_remaining_quantity : list byte;
      bid_total_remaining_quantity : list byte;
      ask_per_type_total_remaining_quantity : list byte;
      bid_per_type_total_remaining_quantity : list byte;
      designated_bid_level_1_price : list byte;
      designated_bid_level_1_repo_remaining_quantity : list byte;
      designated_bid_level_1_isin : list byte;
      designated_bid_level_2_price : list byte;
      designated_bid_level_2_repo_remaining_quantity : list byte;
      designated_bid_level_2_isin : list byte;
      designated_bid_level_3_price : list byte;
      designated_bid_level_3_repo_remaining_quantity : list byte;
      designated_bid_level_3_isin : list byte;
      designated_bid_level_4_price : list byte;
      designated_bid_level_4_repo_remaining_quantity : list byte;
      designated_bid_level_4_isin : list byte;
      designated_bid_level_5_price : list byte;
      designated_bid_level_5_repo_remaining_quantity : list byte;
      designated_bid_level_5_isin : list byte;
      designated_bid_level_6_price : list byte;
      designated_bid_level_6_repo_remaining_quantity : list byte;
      designated_bid_level_6_isin : list byte;
      designated_bid_level_7_price : list byte;
      designated_bid_level_7_repo_remaining_quantity : list byte;
      designated_bid_level_7_isin : list byte;
      designated_bid_level_8_price : list byte;
      designated_bid_level_8_repo_remaining_quantity : list byte;
      designated_bid_level_8_isin : list byte;
      designated_bid_level_9_price : list byte;
      designated_bid_level_9_repo_remaining_quantity : list byte;
      designated_bid_level_9_isin : list byte;
      designated_bid_level_10_price : list byte;
      designated_bid_level_10_repo_remaining_quantity : list byte;
      designated_bid_level_10_isin : list byte;
      designated_best_bid_price : list byte;
      net_bid_per_type_total_remaining_quantity : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (trading_price record) = 11 /\
      Datatypes.length (trading_volume record) = 10 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (trading_value record) = 22 /\
      Datatypes.length (ask_repo_type_code record) = 2 /\
      Datatypes.length (ask_duration_of_term_repo record) = 4 /\
      Datatypes.length (bid_repo_type_code record) = 2 /\
      Datatypes.length (bid_duration_of_term_repo record) = 4 /\
      Datatypes.length (opening_price record) = 11 /\
      Datatypes.length (todays_high record) = 11 /\
      Datatypes.length (todays_low record) = 11 /\
      Datatypes.length (category_opening_price record) = 11 /\
      Datatypes.length (category_todays_high record) = 11 /\
      Datatypes.length (category_todays_low record) = 11 /\
      Datatypes.length (accumulated_trading_volume record) = 15 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (category_accumulated_trading_volume record) = 15 /\
      Datatypes.length (category_accumulated_trading_value record) = 22 /\
      Datatypes.length (ask_level_1_price record) = 11 /\
      Datatypes.length (bid_level_1_price record) = 11 /\
      Datatypes.length (ask_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_1_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_1_price record) = 11 /\
      Datatypes.length (total_bid_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_1_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_1_price record) = 11 /\
      Datatypes.length (bid_per_type_level_1_price record) = 11 /\
      Datatypes.length (ask_per_type_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_1_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_1_trading_amount record) = 22 /\
      Datatypes.length (ask_level_2_price record) = 11 /\
      Datatypes.length (bid_level_2_price record) = 11 /\
      Datatypes.length (ask_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_2_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_2_price record) = 11 /\
      Datatypes.length (total_bid_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_2_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_2_price record) = 11 /\
      Datatypes.length (bid_per_type_level_2_price record) = 11 /\
      Datatypes.length (ask_per_type_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_2_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_2_trading_amount record) = 22 /\
      Datatypes.length (ask_level_3_price record) = 11 /\
      Datatypes.length (bid_level_3_price record) = 11 /\
      Datatypes.length (ask_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_3_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_3_price record) = 11 /\
      Datatypes.length (total_bid_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_3_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_3_price record) = 11 /\
      Datatypes.length (bid_per_type_level_3_price record) = 11 /\
      Datatypes.length (ask_per_type_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_3_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_3_trading_amount record) = 22 /\
      Datatypes.length (ask_level_4_price record) = 11 /\
      Datatypes.length (bid_level_4_price record) = 11 /\
      Datatypes.length (ask_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_4_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_4_price record) = 11 /\
      Datatypes.length (total_bid_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_4_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_4_price record) = 11 /\
      Datatypes.length (bid_per_type_level_4_price record) = 11 /\
      Datatypes.length (ask_per_type_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_4_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_4_trading_amount record) = 22 /\
      Datatypes.length (ask_level_5_price record) = 11 /\
      Datatypes.length (bid_level_5_price record) = 11 /\
      Datatypes.length (ask_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_level_5_trading_amount record) = 22 /\
      Datatypes.length (total_bid_level_5_price record) = 11 /\
      Datatypes.length (total_bid_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_level_5_including_gc record) = 1 /\
      Datatypes.length (ask_per_type_level_5_price record) = 11 /\
      Datatypes.length (bid_per_type_level_5_price record) = 11 /\
      Datatypes.length (ask_per_type_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_level_5_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_level_5_trading_amount record) = 22 /\
      Datatypes.length (ask_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_total_remaining_quantity record) = 15 /\
      Datatypes.length (ask_per_type_total_remaining_quantity record) = 15 /\
      Datatypes.length (bid_per_type_total_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_1_price record) = 11 /\
      Datatypes.length (designated_bid_level_1_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_1_isin record) = 12 /\
      Datatypes.length (designated_bid_level_2_price record) = 11 /\
      Datatypes.length (designated_bid_level_2_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_2_isin record) = 12 /\
      Datatypes.length (designated_bid_level_3_price record) = 11 /\
      Datatypes.length (designated_bid_level_3_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_3_isin record) = 12 /\
      Datatypes.length (designated_bid_level_4_price record) = 11 /\
      Datatypes.length (designated_bid_level_4_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_4_isin record) = 12 /\
      Datatypes.length (designated_bid_level_5_price record) = 11 /\
      Datatypes.length (designated_bid_level_5_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_5_isin record) = 12 /\
      Datatypes.length (designated_bid_level_6_price record) = 11 /\
      Datatypes.length (designated_bid_level_6_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_6_isin record) = 12 /\
      Datatypes.length (designated_bid_level_7_price record) = 11 /\
      Datatypes.length (designated_bid_level_7_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_7_isin record) = 12 /\
      Datatypes.length (designated_bid_level_8_price record) = 11 /\
      Datatypes.length (designated_bid_level_8_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_8_isin record) = 12 /\
      Datatypes.length (designated_bid_level_9_price record) = 11 /\
      Datatypes.length (designated_bid_level_9_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_9_isin record) = 12 /\
      Datatypes.length (designated_bid_level_10_price record) = 11 /\
      Datatypes.length (designated_bid_level_10_repo_remaining_quantity record) = 15 /\
      Datatypes.length (designated_bid_level_10_isin record) = 12 /\
      Datatypes.length (designated_best_bid_price record) = 11 /\
      Datatypes.length (net_bid_per_type_total_remaining_quantity record) = 15 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 11 (trading_price record) ++
      encode_bytes 10 (trading_volume record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 22 (trading_value record) ++
      encode_bytes 2 (ask_repo_type_code record) ++
      encode_bytes 4 (ask_duration_of_term_repo record) ++
      encode_bytes 2 (bid_repo_type_code record) ++
      encode_bytes 4 (bid_duration_of_term_repo record) ++
      encode_bytes 11 (opening_price record) ++
      encode_bytes 11 (todays_high record) ++
      encode_bytes 11 (todays_low record) ++
      encode_bytes 11 (category_opening_price record) ++
      encode_bytes 11 (category_todays_high record) ++
      encode_bytes 11 (category_todays_low record) ++
      encode_bytes 15 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 15 (category_accumulated_trading_volume record) ++
      encode_bytes 22 (category_accumulated_trading_value record) ++
      encode_bytes 11 (ask_level_1_price record) ++
      encode_bytes 11 (bid_level_1_price record) ++
      encode_bytes 15 (ask_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_level_1_remaining_quantity record) ++
      encode_bytes 22 (ask_level_1_trading_amount record) ++
      encode_bytes 11 (total_bid_level_1_price record) ++
      encode_bytes 15 (total_bid_level_1_remaining_quantity record) ++
      encode_bytes 1 (bid_level_1_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_1_price record) ++
      encode_bytes 11 (bid_per_type_level_1_price record) ++
      encode_bytes 15 (ask_per_type_level_1_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_1_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_1_trading_amount record) ++
      encode_bytes 11 (ask_level_2_price record) ++
      encode_bytes 11 (bid_level_2_price record) ++
      encode_bytes 15 (ask_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_level_2_remaining_quantity record) ++
      encode_bytes 22 (ask_level_2_trading_amount record) ++
      encode_bytes 11 (total_bid_level_2_price record) ++
      encode_bytes 15 (total_bid_level_2_remaining_quantity record) ++
      encode_bytes 1 (bid_level_2_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_2_price record) ++
      encode_bytes 11 (bid_per_type_level_2_price record) ++
      encode_bytes 15 (ask_per_type_level_2_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_2_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_2_trading_amount record) ++
      encode_bytes 11 (ask_level_3_price record) ++
      encode_bytes 11 (bid_level_3_price record) ++
      encode_bytes 15 (ask_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_level_3_remaining_quantity record) ++
      encode_bytes 22 (ask_level_3_trading_amount record) ++
      encode_bytes 11 (total_bid_level_3_price record) ++
      encode_bytes 15 (total_bid_level_3_remaining_quantity record) ++
      encode_bytes 1 (bid_level_3_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_3_price record) ++
      encode_bytes 11 (bid_per_type_level_3_price record) ++
      encode_bytes 15 (ask_per_type_level_3_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_3_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_3_trading_amount record) ++
      encode_bytes 11 (ask_level_4_price record) ++
      encode_bytes 11 (bid_level_4_price record) ++
      encode_bytes 15 (ask_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_level_4_remaining_quantity record) ++
      encode_bytes 22 (ask_level_4_trading_amount record) ++
      encode_bytes 11 (total_bid_level_4_price record) ++
      encode_bytes 15 (total_bid_level_4_remaining_quantity record) ++
      encode_bytes 1 (bid_level_4_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_4_price record) ++
      encode_bytes 11 (bid_per_type_level_4_price record) ++
      encode_bytes 15 (ask_per_type_level_4_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_4_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_4_trading_amount record) ++
      encode_bytes 11 (ask_level_5_price record) ++
      encode_bytes 11 (bid_level_5_price record) ++
      encode_bytes 15 (ask_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_level_5_remaining_quantity record) ++
      encode_bytes 22 (ask_level_5_trading_amount record) ++
      encode_bytes 11 (total_bid_level_5_price record) ++
      encode_bytes 15 (total_bid_level_5_remaining_quantity record) ++
      encode_bytes 1 (bid_level_5_including_gc record) ++
      encode_bytes 11 (ask_per_type_level_5_price record) ++
      encode_bytes 11 (bid_per_type_level_5_price record) ++
      encode_bytes 15 (ask_per_type_level_5_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_level_5_remaining_quantity record) ++
      encode_bytes 22 (ask_per_type_level_5_trading_amount record) ++
      encode_bytes 15 (ask_total_remaining_quantity record) ++
      encode_bytes 15 (bid_total_remaining_quantity record) ++
      encode_bytes 15 (ask_per_type_total_remaining_quantity record) ++
      encode_bytes 15 (bid_per_type_total_remaining_quantity record) ++
      encode_bytes 11 (designated_bid_level_1_price record) ++
      encode_bytes 15 (designated_bid_level_1_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_1_isin record) ++
      encode_bytes 11 (designated_bid_level_2_price record) ++
      encode_bytes 15 (designated_bid_level_2_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_2_isin record) ++
      encode_bytes 11 (designated_bid_level_3_price record) ++
      encode_bytes 15 (designated_bid_level_3_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_3_isin record) ++
      encode_bytes 11 (designated_bid_level_4_price record) ++
      encode_bytes 15 (designated_bid_level_4_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_4_isin record) ++
      encode_bytes 11 (designated_bid_level_5_price record) ++
      encode_bytes 15 (designated_bid_level_5_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_5_isin record) ++
      encode_bytes 11 (designated_bid_level_6_price record) ++
      encode_bytes 15 (designated_bid_level_6_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_6_isin record) ++
      encode_bytes 11 (designated_bid_level_7_price record) ++
      encode_bytes 15 (designated_bid_level_7_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_7_isin record) ++
      encode_bytes 11 (designated_bid_level_8_price record) ++
      encode_bytes 15 (designated_bid_level_8_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_8_isin record) ++
      encode_bytes 11 (designated_bid_level_9_price record) ++
      encode_bytes 15 (designated_bid_level_9_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_9_isin record) ++
      encode_bytes 11 (designated_bid_level_10_price record) ++
      encode_bytes 15 (designated_bid_level_10_repo_remaining_quantity record) ++
      encode_bytes 12 (designated_bid_level_10_isin record) ++
      encode_bytes 11 (designated_best_bid_price record) ++
      encode_bytes 15 (net_bid_per_type_total_remaining_quantity record) ++
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
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (processing_time_of_trading_system_value, bytes) =>
                          match decode_bytes 11 bytes with
                          | None => None
                          | Some (trading_price_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (trading_volume_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (trading_date_value, bytes) =>
                                      match decode_bytes 22 bytes with
                                      | None => None
                                      | Some (trading_value_value, bytes) =>
                                          match decode_bytes 2 bytes with
                                          | None => None
                                          | Some (ask_repo_type_code_value, bytes) =>
                                              match decode_bytes 4 bytes with
                                              | None => None
                                              | Some (ask_duration_of_term_repo_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (bid_repo_type_code_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (bid_duration_of_term_repo_value, bytes) =>
                                                          match decode_bytes 11 bytes with
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
                                                                      | Some (category_opening_price_value, bytes) =>
                                                                          match decode_bytes 11 bytes with
                                                                          | None => None
                                                                          | Some (category_todays_high_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (category_todays_low_value, bytes) =>
                                                                                  match decode_bytes 15 bytes with
                                                                                  | None => None
                                                                                  | Some (accumulated_trading_volume_value, bytes) =>
                                                                                      match decode_bytes 22 bytes with
                                                                                      | None => None
                                                                                      | Some (accumulated_trading_value_value, bytes) =>
                                                                                          match decode_bytes 15 bytes with
                                                                                          | None => None
                                                                                          | Some (category_accumulated_trading_volume_value, bytes) =>
                                                                                              match decode_bytes 22 bytes with
                                                                                              | None => None
                                                                                              | Some (category_accumulated_trading_value_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_1_price_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_1_price_value, bytes) =>
                                                                                                          match decode_bytes 15 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_1_remaining_quantity_value, bytes) =>
                                                                                                              match decode_bytes 15 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_1_remaining_quantity_value, bytes) =>
                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_1_trading_amount_value, bytes) =>
                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (total_bid_level_1_price_value, bytes) =>
                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (total_bid_level_1_remaining_quantity_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_1_including_gc_value, bytes) =>
                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_per_type_level_1_price_value, bytes) =>
                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_per_type_level_1_price_value, bytes) =>
                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_per_type_level_1_remaining_quantity_value, bytes) =>
                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_per_type_level_1_remaining_quantity_value, bytes) =>
                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_per_type_level_1_trading_amount_value, bytes) =>
                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_level_2_price_value, bytes) =>
                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_level_2_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ask_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (bid_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_level_2_trading_amount_value, bytes) =>
                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (total_bid_level_2_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (total_bid_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (bid_level_2_including_gc_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (ask_per_type_level_2_price_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (bid_per_type_level_2_price_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (ask_per_type_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (bid_per_type_level_2_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 22 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (ask_per_type_level_2_trading_amount_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_level_3_price_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (bid_level_3_price_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (ask_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bid_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (ask_level_3_trading_amount_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (total_bid_level_3_price_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (total_bid_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (bid_level_3_including_gc_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (ask_per_type_level_3_price_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (bid_per_type_level_3_price_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (ask_per_type_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (bid_per_type_level_3_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (ask_per_type_level_3_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (ask_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (bid_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (ask_level_4_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (total_bid_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (total_bid_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (bid_level_4_including_gc_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (ask_per_type_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (bid_per_type_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (ask_per_type_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (bid_per_type_level_4_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (ask_per_type_level_4_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (ask_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (bid_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (ask_level_5_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (total_bid_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (total_bid_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (bid_level_5_including_gc_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (ask_per_type_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (bid_per_type_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (ask_per_type_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (bid_per_type_level_5_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (ask_per_type_level_5_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                      | Some (ask_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                          | Some (bid_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                              | Some (ask_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                  | Some (bid_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_1_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_1_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_1_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_2_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_2_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_2_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_3_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_3_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_3_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_4_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_4_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_4_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_5_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_5_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_5_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_6_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_6_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_6_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_7_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_7_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_7_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_8_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_8_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_9_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_bid_level_9_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designated_bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (designated_bid_level_10_repo_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (designated_bid_level_10_isin_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (designated_best_bid_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (net_bid_per_type_total_remaining_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; trading_date := trading_date_value; trading_value := trading_value_value; ask_repo_type_code := ask_repo_type_code_value; ask_duration_of_term_repo := ask_duration_of_term_repo_value; bid_repo_type_code := bid_repo_type_code_value; bid_duration_of_term_repo := bid_duration_of_term_repo_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; category_opening_price := category_opening_price_value; category_todays_high := category_todays_high_value; category_todays_low := category_todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; category_accumulated_trading_volume := category_accumulated_trading_volume_value; category_accumulated_trading_value := category_accumulated_trading_value_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_remaining_quantity := ask_level_1_remaining_quantity_value; bid_level_1_remaining_quantity := bid_level_1_remaining_quantity_value; ask_level_1_trading_amount := ask_level_1_trading_amount_value; total_bid_level_1_price := total_bid_level_1_price_value; total_bid_level_1_remaining_quantity := total_bid_level_1_remaining_quantity_value; bid_level_1_including_gc := bid_level_1_including_gc_value; ask_per_type_level_1_price := ask_per_type_level_1_price_value; bid_per_type_level_1_price := bid_per_type_level_1_price_value; ask_per_type_level_1_remaining_quantity := ask_per_type_level_1_remaining_quantity_value; bid_per_type_level_1_remaining_quantity := bid_per_type_level_1_remaining_quantity_value; ask_per_type_level_1_trading_amount := ask_per_type_level_1_trading_amount_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_remaining_quantity := ask_level_2_remaining_quantity_value; bid_level_2_remaining_quantity := bid_level_2_remaining_quantity_value; ask_level_2_trading_amount := ask_level_2_trading_amount_value; total_bid_level_2_price := total_bid_level_2_price_value; total_bid_level_2_remaining_quantity := total_bid_level_2_remaining_quantity_value; bid_level_2_including_gc := bid_level_2_including_gc_value; ask_per_type_level_2_price := ask_per_type_level_2_price_value; bid_per_type_level_2_price := bid_per_type_level_2_price_value; ask_per_type_level_2_remaining_quantity := ask_per_type_level_2_remaining_quantity_value; bid_per_type_level_2_remaining_quantity := bid_per_type_level_2_remaining_quantity_value; ask_per_type_level_2_trading_amount := ask_per_type_level_2_trading_amount_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_remaining_quantity := ask_level_3_remaining_quantity_value; bid_level_3_remaining_quantity := bid_level_3_remaining_quantity_value; ask_level_3_trading_amount := ask_level_3_trading_amount_value; total_bid_level_3_price := total_bid_level_3_price_value; total_bid_level_3_remaining_quantity := total_bid_level_3_remaining_quantity_value; bid_level_3_including_gc := bid_level_3_including_gc_value; ask_per_type_level_3_price := ask_per_type_level_3_price_value; bid_per_type_level_3_price := bid_per_type_level_3_price_value; ask_per_type_level_3_remaining_quantity := ask_per_type_level_3_remaining_quantity_value; bid_per_type_level_3_remaining_quantity := bid_per_type_level_3_remaining_quantity_value; ask_per_type_level_3_trading_amount := ask_per_type_level_3_trading_amount_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_remaining_quantity := ask_level_4_remaining_quantity_value; bid_level_4_remaining_quantity := bid_level_4_remaining_quantity_value; ask_level_4_trading_amount := ask_level_4_trading_amount_value; total_bid_level_4_price := total_bid_level_4_price_value; total_bid_level_4_remaining_quantity := total_bid_level_4_remaining_quantity_value; bid_level_4_including_gc := bid_level_4_including_gc_value; ask_per_type_level_4_price := ask_per_type_level_4_price_value; bid_per_type_level_4_price := bid_per_type_level_4_price_value; ask_per_type_level_4_remaining_quantity := ask_per_type_level_4_remaining_quantity_value; bid_per_type_level_4_remaining_quantity := bid_per_type_level_4_remaining_quantity_value; ask_per_type_level_4_trading_amount := ask_per_type_level_4_trading_amount_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_remaining_quantity := ask_level_5_remaining_quantity_value; bid_level_5_remaining_quantity := bid_level_5_remaining_quantity_value; ask_level_5_trading_amount := ask_level_5_trading_amount_value; total_bid_level_5_price := total_bid_level_5_price_value; total_bid_level_5_remaining_quantity := total_bid_level_5_remaining_quantity_value; bid_level_5_including_gc := bid_level_5_including_gc_value; ask_per_type_level_5_price := ask_per_type_level_5_price_value; bid_per_type_level_5_price := bid_per_type_level_5_price_value; ask_per_type_level_5_remaining_quantity := ask_per_type_level_5_remaining_quantity_value; bid_per_type_level_5_remaining_quantity := bid_per_type_level_5_remaining_quantity_value; ask_per_type_level_5_trading_amount := ask_per_type_level_5_trading_amount_value; ask_total_remaining_quantity := ask_total_remaining_quantity_value; bid_total_remaining_quantity := bid_total_remaining_quantity_value; ask_per_type_total_remaining_quantity := ask_per_type_total_remaining_quantity_value; bid_per_type_total_remaining_quantity := bid_per_type_total_remaining_quantity_value; designated_bid_level_1_price := designated_bid_level_1_price_value; designated_bid_level_1_repo_remaining_quantity := designated_bid_level_1_repo_remaining_quantity_value; designated_bid_level_1_isin := designated_bid_level_1_isin_value; designated_bid_level_2_price := designated_bid_level_2_price_value; designated_bid_level_2_repo_remaining_quantity := designated_bid_level_2_repo_remaining_quantity_value; designated_bid_level_2_isin := designated_bid_level_2_isin_value; designated_bid_level_3_price := designated_bid_level_3_price_value; designated_bid_level_3_repo_remaining_quantity := designated_bid_level_3_repo_remaining_quantity_value; designated_bid_level_3_isin := designated_bid_level_3_isin_value; designated_bid_level_4_price := designated_bid_level_4_price_value; designated_bid_level_4_repo_remaining_quantity := designated_bid_level_4_repo_remaining_quantity_value; designated_bid_level_4_isin := designated_bid_level_4_isin_value; designated_bid_level_5_price := designated_bid_level_5_price_value; designated_bid_level_5_repo_remaining_quantity := designated_bid_level_5_repo_remaining_quantity_value; designated_bid_level_5_isin := designated_bid_level_5_isin_value; designated_bid_level_6_price := designated_bid_level_6_price_value; designated_bid_level_6_repo_remaining_quantity := designated_bid_level_6_repo_remaining_quantity_value; designated_bid_level_6_isin := designated_bid_level_6_isin_value; designated_bid_level_7_price := designated_bid_level_7_price_value; designated_bid_level_7_repo_remaining_quantity := designated_bid_level_7_repo_remaining_quantity_value; designated_bid_level_7_isin := designated_bid_level_7_isin_value; designated_bid_level_8_price := designated_bid_level_8_price_value; designated_bid_level_8_repo_remaining_quantity := designated_bid_level_8_repo_remaining_quantity_value; designated_bid_level_8_isin := designated_bid_level_8_isin_value; designated_bid_level_9_price := designated_bid_level_9_price_value; designated_bid_level_9_repo_remaining_quantity := designated_bid_level_9_repo_remaining_quantity_value; designated_bid_level_9_isin := designated_bid_level_9_isin_value; designated_bid_level_10_price := designated_bid_level_10_price_value; designated_bid_level_10_repo_remaining_quantity := designated_bid_level_10_repo_remaining_quantity_value; designated_bid_level_10_isin := designated_bid_level_10_isin_value; designated_best_bid_price := designated_best_bid_price_value; net_bid_per_type_total_remaining_quantity := net_bid_per_type_total_remaining_quantity_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1581.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 [bound_87 [bound_88 [bound_89 [bound_90 [bound_91 [bound_92 [bound_93 [bound_94 [bound_95 [bound_96 [bound_97 [bound_98 [bound_99 [bound_100 [bound_101 [bound_102 [bound_103 [bound_104 [bound_105 [bound_106 [bound_107 [bound_108 [bound_109 [bound_110 [bound_111 [bound_112 [bound_113 [bound_114 [bound_115 [bound_116 [bound_117 [bound_118 [bound_119 [bound_120 [bound_121 [bound_122 [bound_123 bound_124]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_107.
      rewrite decode_encode_bytes by exact bound_108.
      rewrite decode_encode_bytes by exact bound_109.
      rewrite decode_encode_bytes by exact bound_110.
      rewrite decode_encode_bytes by exact bound_111.
      rewrite decode_encode_bytes by exact bound_112.
      rewrite decode_encode_bytes by exact bound_113.
      rewrite decode_encode_bytes by exact bound_114.
      rewrite decode_encode_bytes by exact bound_115.
      rewrite decode_encode_bytes by exact bound_116.
      rewrite decode_encode_bytes by exact bound_117.
      rewrite decode_encode_bytes by exact bound_118.
      rewrite decode_encode_bytes by exact bound_119.
      rewrite decode_encode_bytes by exact bound_120.
      rewrite decode_encode_bytes by exact bound_121.
      rewrite decode_encode_bytes by exact bound_122.
      rewrite decode_encode_bytes by exact bound_123.
      rewrite decode_encode_uint by exact bound_124.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RepoOrderFilledPlusQuoteMessage.

End KoscomMdcsRealtimeBondAV2020.
