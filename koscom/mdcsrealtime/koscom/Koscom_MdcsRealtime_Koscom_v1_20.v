From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Koscom Co., Ltd. MDCS Realtime Koscom

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

Module KoscomMdcsRealtimeKoscomV120.

  Module KOtcIssueClosingMessage.

    (** K-OTC Issue Closing. Reports closing price and the quotation category per ISIN. *)
    Record t := {
      isin : list byte;
      data_seq_number : list byte;
      closing_price : list byte;
      quotation_category : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_seq_number record) = 8 /\
      Datatypes.length (closing_price record) = 9 /\
      Datatypes.length (quotation_category record) = 1 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (data_seq_number record) ++
      encode_bytes 9 (closing_price record) ++
      encode_bytes 1 (quotation_category record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (data_seq_number_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (closing_price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quotation_category_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (filler_4_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| isin := isin_value; data_seq_number := data_seq_number_value; closing_price := closing_price_value; quotation_category := quotation_category_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
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

  End KOtcIssueClosingMessage.

  Module KOtcMarketOperationMessage.

    (** K-OTC Market Operation. Trading halt / lift-after-halt events with reason code. *)
    Record t := {
      isin : list byte;
      data_seq_number : list byte;
      type : list byte;
      reason : list byte;
      filler_1 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_seq_number record) = 8 /\
      Datatypes.length (type record) = 1 /\
      Datatypes.length (reason record) = 2 /\
      Datatypes.length (filler_1 record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (data_seq_number record) ++
      encode_bytes 1 (type record) ++
      encode_bytes 2 (reason record) ++
      encode_bytes 1 (filler_1 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (data_seq_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (type_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (filler_1_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| isin := isin_value; data_seq_number := data_seq_number_value; type := type_value; reason := reason_value; filler_1 := filler_1_value; end_keyword := end_keyword_value |}, bytes)
                          end
                      end
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

  End KOtcMarketOperationMessage.

  Module KOtcMarketActionMessage.

    (** K-OTC Market Action. Basis price and upper/lower limit price changes. *)
    Record t := {
      isin_nullable : list byte;
      data_type : list byte;
      change_date : list byte;
      change_time : list byte;
      basis_price_before_action : list byte;
      upper_limit_price_before_action : list byte;
      lower_limit_price_before_action : list byte;
      basis_price_after_action : list byte;
      upper_limit_price_after_action : list byte;
      lower_limit_price_after_action : list byte;
      filler_10 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_nullable record) = 12 /\
      Datatypes.length (data_type record) = 2 /\
      Datatypes.length (change_date record) = 8 /\
      Datatypes.length (change_time record) = 8 /\
      Datatypes.length (basis_price_before_action record) = 9 /\
      Datatypes.length (upper_limit_price_before_action record) = 9 /\
      Datatypes.length (lower_limit_price_before_action record) = 9 /\
      Datatypes.length (basis_price_after_action record) = 9 /\
      Datatypes.length (upper_limit_price_after_action record) = 9 /\
      Datatypes.length (lower_limit_price_after_action record) = 9 /\
      Datatypes.length (filler_10 record) = 10 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_nullable record) ++
      encode_bytes 2 (data_type record) ++
      encode_bytes 8 (change_date record) ++
      encode_bytes 8 (change_time record) ++
      encode_bytes 9 (basis_price_before_action record) ++
      encode_bytes 9 (upper_limit_price_before_action record) ++
      encode_bytes 9 (lower_limit_price_before_action record) ++
      encode_bytes 9 (basis_price_after_action record) ++
      encode_bytes 9 (upper_limit_price_after_action record) ++
      encode_bytes 9 (lower_limit_price_after_action record) ++
      encode_bytes 10 (filler_10 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_nullable_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (data_type_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (change_date_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (change_time_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (basis_price_before_action_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (upper_limit_price_before_action_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (lower_limit_price_before_action_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (basis_price_after_action_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (upper_limit_price_after_action_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (lower_limit_price_after_action_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (filler_10_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (end_keyword_value, bytes) =>
                                                      Some ({| isin_nullable := isin_nullable_value; data_type := data_type_value; change_date := change_date_value; change_time := change_time_value; basis_price_before_action := basis_price_before_action_value; upper_limit_price_before_action := upper_limit_price_before_action_value; lower_limit_price_before_action := lower_limit_price_before_action_value; basis_price_after_action := basis_price_after_action_value; upper_limit_price_after_action := upper_limit_price_after_action_value; lower_limit_price_after_action := lower_limit_price_after_action_value; filler_10 := filler_10_value; end_keyword := end_keyword_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 95.
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

  End KOtcMarketActionMessage.

  Module KOtcQuoteMessage.

    (** K-OTC Quote. Bid/ask quote with remaining quantity at the best price. *)
    Record t := {
      isin : list byte;
      data_seq_number : list byte;
      process_type : list byte;
      quote_number : list byte;
      original_quote_number : list byte;
      original_quote_price : list byte;
      bidask_type : list byte;
      price : list byte;
      quantity : list byte;
      subscription_time : list byte;
      total_remaining_quantity_of_ask : list byte;
      total_remaining_quantity_of_bid : list byte;
      ask_best_order : list byte;
      remaining_quantity_of_ask_best_order : list byte;
      bid_best_order : list byte;
      remaining_quantity_of_bid_best_order : list byte;
      price_compare_remaining_quantity_of_order : list byte;
      original_price_compare_remaining_quantity_of_order : list byte;
      securities_company_number : list byte;
      branch_name : list byte;
      filler_33 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_seq_number record) = 8 /\
      Datatypes.length (process_type record) = 1 /\
      Datatypes.length (quote_number record) = 6 /\
      Datatypes.length (original_quote_number record) = 6 /\
      Datatypes.length (original_quote_price record) = 9 /\
      Datatypes.length (bidask_type record) = 1 /\
      Datatypes.length (price record) = 9 /\
      Datatypes.length (quantity record) = 10 /\
      Datatypes.length (subscription_time record) = 6 /\
      Datatypes.length (total_remaining_quantity_of_ask record) = 10 /\
      Datatypes.length (total_remaining_quantity_of_bid record) = 10 /\
      Datatypes.length (ask_best_order record) = 9 /\
      Datatypes.length (remaining_quantity_of_ask_best_order record) = 10 /\
      Datatypes.length (bid_best_order record) = 9 /\
      Datatypes.length (remaining_quantity_of_bid_best_order record) = 10 /\
      Datatypes.length (price_compare_remaining_quantity_of_order record) = 10 /\
      Datatypes.length (original_price_compare_remaining_quantity_of_order record) = 10 /\
      Datatypes.length (securities_company_number record) = 3 /\
      Datatypes.length (branch_name record) = 12 /\
      Datatypes.length (filler_33 record) = 33 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (data_seq_number record) ++
      encode_bytes 1 (process_type record) ++
      encode_bytes 6 (quote_number record) ++
      encode_bytes 6 (original_quote_number record) ++
      encode_bytes 9 (original_quote_price record) ++
      encode_bytes 1 (bidask_type record) ++
      encode_bytes 9 (price record) ++
      encode_bytes 10 (quantity record) ++
      encode_bytes 6 (subscription_time record) ++
      encode_bytes 10 (total_remaining_quantity_of_ask record) ++
      encode_bytes 10 (total_remaining_quantity_of_bid record) ++
      encode_bytes 9 (ask_best_order record) ++
      encode_bytes 10 (remaining_quantity_of_ask_best_order record) ++
      encode_bytes 9 (bid_best_order record) ++
      encode_bytes 10 (remaining_quantity_of_bid_best_order record) ++
      encode_bytes 10 (price_compare_remaining_quantity_of_order record) ++
      encode_bytes 10 (original_price_compare_remaining_quantity_of_order record) ++
      encode_bytes 3 (securities_company_number record) ++
      encode_bytes 12 (branch_name record) ++
      encode_bytes 33 (filler_33 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (data_seq_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (process_type_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (quote_number_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (original_quote_number_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (original_quote_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (bidask_type_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (quantity_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (subscription_time_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (total_remaining_quantity_of_ask_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (total_remaining_quantity_of_bid_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (ask_best_order_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (remaining_quantity_of_ask_best_order_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (bid_best_order_value, bytes) =>
                                                                  match decode_bytes 10 bytes with
                                                                  | None => None
                                                                  | Some (remaining_quantity_of_bid_best_order_value, bytes) =>
                                                                      match decode_bytes 10 bytes with
                                                                      | None => None
                                                                      | Some (price_compare_remaining_quantity_of_order_value, bytes) =>
                                                                          match decode_bytes 10 bytes with
                                                                          | None => None
                                                                          | Some (original_price_compare_remaining_quantity_of_order_value, bytes) =>
                                                                              match decode_bytes 3 bytes with
                                                                              | None => None
                                                                              | Some (securities_company_number_value, bytes) =>
                                                                                  match decode_bytes 12 bytes with
                                                                                  | None => None
                                                                                  | Some (branch_name_value, bytes) =>
                                                                                      match decode_bytes 33 bytes with
                                                                                      | None => None
                                                                                      | Some (filler_33_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                              Some ({| isin := isin_value; data_seq_number := data_seq_number_value; process_type := process_type_value; quote_number := quote_number_value; original_quote_number := original_quote_number_value; original_quote_price := original_quote_price_value; bidask_type := bidask_type_value; price := price_value; quantity := quantity_value; subscription_time := subscription_time_value; total_remaining_quantity_of_ask := total_remaining_quantity_of_ask_value; total_remaining_quantity_of_bid := total_remaining_quantity_of_bid_value; ask_best_order := ask_best_order_value; remaining_quantity_of_ask_best_order := remaining_quantity_of_ask_best_order_value; bid_best_order := bid_best_order_value; remaining_quantity_of_bid_best_order := remaining_quantity_of_bid_best_order_value; price_compare_remaining_quantity_of_order := price_compare_remaining_quantity_of_order_value; original_price_compare_remaining_quantity_of_order := original_price_compare_remaining_quantity_of_order_value; securities_company_number := securities_company_number_value; branch_name := branch_name_value; filler_33 := filler_33_value; end_keyword := end_keyword_value |}, bytes)
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 195.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End KOtcQuoteMessage.

  Module KOtcOrderFilledMessage.

    (** K-OTC Order Filled. Trade prints with running totals, high/low, weighted average price, and previous-day comparison. *)
    Record t := {
      isin : list byte;
      data_seq_number : list byte;
      trading_number : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      trading_time : list byte;
      ask_quote_number : list byte;
      bid_quote_number : list byte;
      high_price : list byte;
      low_price : list byte;
      weighted_average_stock_price : list byte;
      total_trading_accumulated_volume : list byte;
      total_trading_accumulated_value : list byte;
      total_remaining_quantity_of_ask : list byte;
      total_remaining_quantity_of_bid : list byte;
      best_ask_order : list byte;
      remaining_quantity_of_best_ask_order : list byte;
      best_bid_order : list byte;
      remaining_quantity_of_best_bid_order : list byte;
      compared_to_previous_day_type : list byte;
      compared_to_previous_day : list byte;
      trading_price_compare_remaining_quantity_of_ask : list byte;
      trading_price_compare_remaining_quantity_of_bid : list byte;
      filler_40 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_seq_number record) = 8 /\
      Datatypes.length (trading_number record) = 6 /\
      Datatypes.length (trading_price record) = 9 /\
      Datatypes.length (trading_volume record) = 12 /\
      Datatypes.length (trading_time record) = 6 /\
      Datatypes.length (ask_quote_number record) = 6 /\
      Datatypes.length (bid_quote_number record) = 6 /\
      Datatypes.length (high_price record) = 9 /\
      Datatypes.length (low_price record) = 9 /\
      Datatypes.length (weighted_average_stock_price record) = 9 /\
      Datatypes.length (total_trading_accumulated_volume record) = 12 /\
      Datatypes.length (total_trading_accumulated_value record) = 14 /\
      Datatypes.length (total_remaining_quantity_of_ask record) = 10 /\
      Datatypes.length (total_remaining_quantity_of_bid record) = 10 /\
      Datatypes.length (best_ask_order record) = 9 /\
      Datatypes.length (remaining_quantity_of_best_ask_order record) = 10 /\
      Datatypes.length (best_bid_order record) = 9 /\
      Datatypes.length (remaining_quantity_of_best_bid_order record) = 10 /\
      Datatypes.length (compared_to_previous_day_type record) = 1 /\
      Datatypes.length (compared_to_previous_day record) = 9 /\
      Datatypes.length (trading_price_compare_remaining_quantity_of_ask record) = 10 /\
      Datatypes.length (trading_price_compare_remaining_quantity_of_bid record) = 10 /\
      Datatypes.length (filler_40 record) = 40 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (data_seq_number record) ++
      encode_bytes 6 (trading_number record) ++
      encode_bytes 9 (trading_price record) ++
      encode_bytes 12 (trading_volume record) ++
      encode_bytes 6 (trading_time record) ++
      encode_bytes 6 (ask_quote_number record) ++
      encode_bytes 6 (bid_quote_number record) ++
      encode_bytes 9 (high_price record) ++
      encode_bytes 9 (low_price record) ++
      encode_bytes 9 (weighted_average_stock_price record) ++
      encode_bytes 12 (total_trading_accumulated_volume record) ++
      encode_bytes 14 (total_trading_accumulated_value record) ++
      encode_bytes 10 (total_remaining_quantity_of_ask record) ++
      encode_bytes 10 (total_remaining_quantity_of_bid record) ++
      encode_bytes 9 (best_ask_order record) ++
      encode_bytes 10 (remaining_quantity_of_best_ask_order record) ++
      encode_bytes 9 (best_bid_order record) ++
      encode_bytes 10 (remaining_quantity_of_best_bid_order record) ++
      encode_bytes 1 (compared_to_previous_day_type record) ++
      encode_bytes 9 (compared_to_previous_day record) ++
      encode_bytes 10 (trading_price_compare_remaining_quantity_of_ask record) ++
      encode_bytes 10 (trading_price_compare_remaining_quantity_of_bid record) ++
      encode_bytes 40 (filler_40 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (data_seq_number_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (trading_number_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (trading_price_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (trading_volume_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (trading_time_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (ask_quote_number_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (bid_quote_number_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (high_price_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (low_price_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (weighted_average_stock_price_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (total_trading_accumulated_volume_value, bytes) =>
                                                      match decode_bytes 14 bytes with
                                                      | None => None
                                                      | Some (total_trading_accumulated_value_value, bytes) =>
                                                          match decode_bytes 10 bytes with
                                                          | None => None
                                                          | Some (total_remaining_quantity_of_ask_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (total_remaining_quantity_of_bid_value, bytes) =>
                                                                  match decode_bytes 9 bytes with
                                                                  | None => None
                                                                  | Some (best_ask_order_value, bytes) =>
                                                                      match decode_bytes 10 bytes with
                                                                      | None => None
                                                                      | Some (remaining_quantity_of_best_ask_order_value, bytes) =>
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (best_bid_order_value, bytes) =>
                                                                              match decode_bytes 10 bytes with
                                                                              | None => None
                                                                              | Some (remaining_quantity_of_best_bid_order_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (compared_to_previous_day_type_value, bytes) =>
                                                                                      match decode_bytes 9 bytes with
                                                                                      | None => None
                                                                                      | Some (compared_to_previous_day_value, bytes) =>
                                                                                          match decode_bytes 10 bytes with
                                                                                          | None => None
                                                                                          | Some (trading_price_compare_remaining_quantity_of_ask_value, bytes) =>
                                                                                              match decode_bytes 10 bytes with
                                                                                              | None => None
                                                                                              | Some (trading_price_compare_remaining_quantity_of_bid_value, bytes) =>
                                                                                                  match decode_bytes 40 bytes with
                                                                                                  | None => None
                                                                                                  | Some (filler_40_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                          Some ({| isin := isin_value; data_seq_number := data_seq_number_value; trading_number := trading_number_value; trading_price := trading_price_value; trading_volume := trading_volume_value; trading_time := trading_time_value; ask_quote_number := ask_quote_number_value; bid_quote_number := bid_quote_number_value; high_price := high_price_value; low_price := low_price_value; weighted_average_stock_price := weighted_average_stock_price_value; total_trading_accumulated_volume := total_trading_accumulated_volume_value; total_trading_accumulated_value := total_trading_accumulated_value_value; total_remaining_quantity_of_ask := total_remaining_quantity_of_ask_value; total_remaining_quantity_of_bid := total_remaining_quantity_of_bid_value; best_ask_order := best_ask_order_value; remaining_quantity_of_best_ask_order := remaining_quantity_of_best_ask_order_value; best_bid_order := best_bid_order_value; remaining_quantity_of_best_bid_order := remaining_quantity_of_best_bid_order_value; compared_to_previous_day_type := compared_to_previous_day_type_value; compared_to_previous_day := compared_to_previous_day_value; trading_price_compare_remaining_quantity_of_ask := trading_price_compare_remaining_quantity_of_ask_value; trading_price_compare_remaining_quantity_of_bid := trading_price_compare_remaining_quantity_of_bid_value; filler_40 := filler_40_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 247.
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

  End KOtcOrderFilledMessage.

  Module OtcBondTradedInfoMessage.

    (** OTC Bond Traded Information. Reports today's or prior-day trading history with volume, pretax unit price, yield, settlement date, and FX category. *)
    Record t := {
      isin : list byte;
      subcategory : list byte;
      trading_date : list byte;
      registered_time : list byte;
      process_category : list byte;
      registered_number : list byte;
      originally_registered_number : list byte;
      trading_type_category : list byte;
      volume : list byte;
      pretax_unit_price : list byte;
      pretax_yield : list byte;
      settlement_date_otc : list byte;
      market_base_rate : list byte;
      fx_category : list byte;
      based_fx : list byte;
      trading_category : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (subcategory record) = 2 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (registered_time record) = 6 /\
      Datatypes.length (process_category record) = 1 /\
      Datatypes.length (registered_number record) = 8 /\
      Datatypes.length (originally_registered_number record) = 8 /\
      Datatypes.length (trading_type_category record) = 1 /\
      Datatypes.length (volume record) = 16 /\
      Datatypes.length (pretax_unit_price record) = 8 /\
      Datatypes.length (pretax_yield record) = 8 /\
      Datatypes.length (settlement_date_otc record) = 8 /\
      Datatypes.length (market_base_rate record) = 8 /\
      Datatypes.length (fx_category record) = 1 /\
      Datatypes.length (based_fx record) = 8 /\
      Datatypes.length (trading_category record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 2 (subcategory record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 6 (registered_time record) ++
      encode_bytes 1 (process_category record) ++
      encode_bytes 8 (registered_number record) ++
      encode_bytes 8 (originally_registered_number record) ++
      encode_bytes 1 (trading_type_category record) ++
      encode_bytes 16 (volume record) ++
      encode_bytes 8 (pretax_unit_price record) ++
      encode_bytes 8 (pretax_yield record) ++
      encode_bytes 8 (settlement_date_otc record) ++
      encode_bytes 8 (market_base_rate record) ++
      encode_bytes 1 (fx_category record) ++
      encode_bytes 8 (based_fx record) ++
      encode_bytes 1 (trading_category record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (subcategory_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trading_date_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (registered_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (process_category_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (registered_number_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (originally_registered_number_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trading_type_category_value, bytes) =>
                                      match decode_bytes 16 bytes with
                                      | None => None
                                      | Some (volume_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (pretax_unit_price_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (pretax_yield_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (settlement_date_otc_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (market_base_rate_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (fx_category_value, bytes) =>
                                                              match decode_bytes 8 bytes with
                                                              | None => None
                                                              | Some (based_fx_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (trading_category_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (end_keyword_value, bytes) =>
                                                                          Some ({| isin := isin_value; subcategory := subcategory_value; trading_date := trading_date_value; registered_time := registered_time_value; process_category := process_category_value; registered_number := registered_number_value; originally_registered_number := originally_registered_number_value; trading_type_category := trading_type_category_value; volume := volume_value; pretax_unit_price := pretax_unit_price_value; pretax_yield := pretax_yield_value; settlement_date_otc := settlement_date_otc_value; market_base_rate := market_base_rate_value; fx_category := fx_category_value; based_fx := based_fx_value; trading_category := trading_category_value; end_keyword := end_keyword_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
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

  End OtcBondTradedInfoMessage.

  Module OtcBondTradesPerInstitutionMessage.

    (** OTC Bond trade aggregates per institution. Reports bid and ask yields and trading volumes/values per institution code and bond type. *)
    Record t := {
      data_process_category : list byte;
      date : list byte;
      institution_code : list byte;
      bond_type_code : list byte;
      ask_yield_institution : list byte;
      ask_trading_volume_institution : list byte;
      ask_trading_value_institution : list byte;
      bid_yield_institution : list byte;
      bid_trading_volume_institution : list byte;
      bid_trading_value_institution : list byte;
      filler_11 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (data_process_category record) = 1 /\
      Datatypes.length (date record) = 8 /\
      Datatypes.length (institution_code record) = 4 /\
      Datatypes.length (bond_type_code record) = 4 /\
      Datatypes.length (ask_yield_institution record) = 8 /\
      Datatypes.length (ask_trading_volume_institution record) = 15 /\
      Datatypes.length (ask_trading_value_institution record) = 15 /\
      Datatypes.length (bid_yield_institution record) = 8 /\
      Datatypes.length (bid_trading_volume_institution record) = 15 /\
      Datatypes.length (bid_trading_value_institution record) = 15 /\
      Datatypes.length (filler_11 record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (data_process_category record) ++
      encode_bytes 8 (date record) ++
      encode_bytes 4 (institution_code record) ++
      encode_bytes 4 (bond_type_code record) ++
      encode_bytes 8 (ask_yield_institution record) ++
      encode_bytes 15 (ask_trading_volume_institution record) ++
      encode_bytes 15 (ask_trading_value_institution record) ++
      encode_bytes 8 (bid_yield_institution record) ++
      encode_bytes 15 (bid_trading_volume_institution record) ++
      encode_bytes 15 (bid_trading_value_institution record) ++
      encode_bytes 11 (filler_11 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (data_process_category_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (date_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (institution_code_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (bond_type_code_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (ask_yield_institution_value, bytes) =>
                          match decode_bytes 15 bytes with
                          | None => None
                          | Some (ask_trading_volume_institution_value, bytes) =>
                              match decode_bytes 15 bytes with
                              | None => None
                              | Some (ask_trading_value_institution_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (bid_yield_institution_value, bytes) =>
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (bid_trading_volume_institution_value, bytes) =>
                                          match decode_bytes 15 bytes with
                                          | None => None
                                          | Some (bid_trading_value_institution_value, bytes) =>
                                              match decode_bytes 11 bytes with
                                              | None => None
                                              | Some (filler_11_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (end_keyword_value, bytes) =>
                                                      Some ({| data_process_category := data_process_category_value; date := date_value; institution_code := institution_code_value; bond_type_code := bond_type_code_value; ask_yield_institution := ask_yield_institution_value; ask_trading_volume_institution := ask_trading_volume_institution_value; ask_trading_value_institution := ask_trading_value_institution_value; bid_yield_institution := bid_yield_institution_value; bid_trading_volume_institution := bid_trading_volume_institution_value; bid_trading_value_institution := bid_trading_value_institution_value; filler_11 := filler_11_value; end_keyword := end_keyword_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
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

  End OtcBondTradesPerInstitutionMessage.

  Module OtcBondTypesPerInvestorMessage.

    (** OTC Bond trade aggregates per investor category. Bid/ask yields and trading volumes/values per ISIN and investor category. *)
    Record t := {
      isin : list byte;
      sequence_number : list byte;
      trading_date : list byte;
      investor_category : list byte;
      ask_yield_investor : list byte;
      bid_yield_investor : list byte;
      ask_trading_volume_investor : list byte;
      bid_trading_volume_investor : list byte;
      ask_trading_value_investor : list byte;
      bid_trading_value_investor : list byte;
      filler_2 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (sequence_number record) = 8 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (investor_category record) = 4 /\
      Datatypes.length (ask_yield_investor record) = 10 /\
      Datatypes.length (bid_yield_investor record) = 10 /\
      Datatypes.length (ask_trading_volume_investor record) = 20 /\
      Datatypes.length (bid_trading_volume_investor record) = 20 /\
      Datatypes.length (ask_trading_value_investor record) = 20 /\
      Datatypes.length (bid_trading_value_investor record) = 20 /\
      Datatypes.length (filler_2 record) = 2 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (sequence_number record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 4 (investor_category record) ++
      encode_bytes 10 (ask_yield_investor record) ++
      encode_bytes 10 (bid_yield_investor record) ++
      encode_bytes 20 (ask_trading_volume_investor record) ++
      encode_bytes 20 (bid_trading_volume_investor record) ++
      encode_bytes 20 (ask_trading_value_investor record) ++
      encode_bytes 20 (bid_trading_value_investor record) ++
      encode_bytes 2 (filler_2 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (trading_date_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (investor_category_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (ask_yield_investor_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (bid_yield_investor_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (ask_trading_volume_investor_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (bid_trading_volume_investor_value, bytes) =>
                                      match decode_bytes 20 bytes with
                                      | None => None
                                      | Some (ask_trading_value_investor_value, bytes) =>
                                          match decode_bytes 20 bytes with
                                          | None => None
                                          | Some (bid_trading_value_investor_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (filler_2_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (end_keyword_value, bytes) =>
                                                      Some ({| isin := isin_value; sequence_number := sequence_number_value; trading_date := trading_date_value; investor_category := investor_category_value; ask_yield_investor := ask_yield_investor_value; bid_yield_investor := bid_yield_investor_value; ask_trading_volume_investor := ask_trading_volume_investor_value; bid_trading_volume_investor := bid_trading_volume_investor_value; ask_trading_value_investor := ask_trading_value_investor_value; bid_trading_value_investor := bid_trading_value_investor_value; filler_2 := filler_2_value; end_keyword := end_keyword_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 135.
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

  End OtcBondTypesPerInvestorMessage.

  Module KBondMessage.

    (** K-BOND dissemination. Quotes and trades with profit rate or price, contract category, settlement date, and replacement order details. *)
    Record t := {
      isin : list byte;
      data_small_category : list byte;
      data_source_type : list byte;
      sequence_number : list byte;
      original_sequence_number : list byte;
      replacement_type : list byte;
      previous_isin_of_replacement : list byte;
      input_date : list byte;
      quotes_offer_time : list byte;
      bond_type_name : list byte;
      change_category : list byte;
      market_data_type : list byte;
      profit_rate_quotes_trading : list byte;
      price_quotes_trading : list byte;
      contract_category : list byte;
      quotes_amount : list byte;
      contract_date : list byte;
      settlement_date_k_bond : list byte;
      filler_11 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_small_category record) = 2 /\
      Datatypes.length (data_source_type record) = 1 /\
      Datatypes.length (sequence_number record) = 8 /\
      Datatypes.length (original_sequence_number record) = 8 /\
      Datatypes.length (replacement_type record) = 1 /\
      Datatypes.length (previous_isin_of_replacement record) = 8 /\
      Datatypes.length (input_date record) = 8 /\
      Datatypes.length (quotes_offer_time record) = 6 /\
      Datatypes.length (bond_type_name record) = 40 /\
      Datatypes.length (change_category record) = 1 /\
      Datatypes.length (market_data_type record) = 1 /\
      Datatypes.length (profit_rate_quotes_trading record) = 8 /\
      Datatypes.length (price_quotes_trading record) = 8 /\
      Datatypes.length (contract_category record) = 1 /\
      Datatypes.length (quotes_amount record) = 16 /\
      Datatypes.length (contract_date record) = 2 /\
      Datatypes.length (settlement_date_k_bond record) = 2 /\
      Datatypes.length (filler_11 record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 2 (data_small_category record) ++
      encode_bytes 1 (data_source_type record) ++
      encode_bytes 8 (sequence_number record) ++
      encode_bytes 8 (original_sequence_number record) ++
      encode_bytes 1 (replacement_type record) ++
      encode_bytes 8 (previous_isin_of_replacement record) ++
      encode_bytes 8 (input_date record) ++
      encode_bytes 6 (quotes_offer_time record) ++
      encode_bytes 40 (bond_type_name record) ++
      encode_bytes 1 (change_category record) ++
      encode_bytes 1 (market_data_type record) ++
      encode_bytes 8 (profit_rate_quotes_trading record) ++
      encode_bytes 8 (price_quotes_trading record) ++
      encode_bytes 1 (contract_category record) ++
      encode_bytes 16 (quotes_amount record) ++
      encode_bytes 2 (contract_date record) ++
      encode_bytes 2 (settlement_date_k_bond record) ++
      encode_bytes 11 (filler_11 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (data_small_category_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (data_source_type_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (original_sequence_number_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (replacement_type_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (previous_isin_of_replacement_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (input_date_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (quotes_offer_time_value, bytes) =>
                                          match decode_bytes 40 bytes with
                                          | None => None
                                          | Some (bond_type_name_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (change_category_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (market_data_type_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (profit_rate_quotes_trading_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (price_quotes_trading_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (contract_category_value, bytes) =>
                                                                  match decode_bytes 16 bytes with
                                                                  | None => None
                                                                  | Some (quotes_amount_value, bytes) =>
                                                                      match decode_bytes 2 bytes with
                                                                      | None => None
                                                                      | Some (contract_date_value, bytes) =>
                                                                          match decode_bytes 2 bytes with
                                                                          | None => None
                                                                          | Some (settlement_date_k_bond_value, bytes) =>
                                                                              match decode_bytes 11 bytes with
                                                                              | None => None
                                                                              | Some (filler_11_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                      Some ({| isin := isin_value; data_small_category := data_small_category_value; data_source_type := data_source_type_value; sequence_number := sequence_number_value; original_sequence_number := original_sequence_number_value; replacement_type := replacement_type_value; previous_isin_of_replacement := previous_isin_of_replacement_value; input_date := input_date_value; quotes_offer_time := quotes_offer_time_value; bond_type_name := bond_type_name_value; change_category := change_category_value; market_data_type := market_data_type_value; profit_rate_quotes_trading := profit_rate_quotes_trading_value; price_quotes_trading := price_quotes_trading_value; contract_category := contract_category_value; quotes_amount := quotes_amount_value; contract_date := contract_date_value; settlement_date_k_bond := settlement_date_k_bond_value; filler_11 := filler_11_value; end_keyword := end_keyword_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 145.
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

  End KBondMessage.

  Module MkfIndexMessage.

    (** MKF Index real-time message. Reports current index value, sign and magnitude of change against the previous day, and accumulated trading volume and value for one MKF index identifier. *)
    Record t := {
      index_id : list byte;
      isin : list byte;
      time : list byte;
      index : list byte;
      sign : list byte;
      comparison : list byte;
      trading_volume : list byte;
      trading_value : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (comparison record) = 9 /\
      Datatypes.length (trading_volume record) = 12 /\
      Datatypes.length (trading_value record) = 12 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 9 (comparison record) ++
      encode_bytes 12 (trading_volume record) ++
      encode_bytes 12 (trading_value record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (index_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (index_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (sign_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (comparison_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (trading_volume_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (trading_value_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (filler_4_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| index_id := index_id_value; isin := isin_value; time := time_value; index := index_value; sign := sign_value; comparison := comparison_value; trading_volume := trading_volume_value; trading_value := trading_value_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
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

  End MkfIndexMessage.

  Module MkfIndexJpyMessage.

    (** MKF Index real-time message with the Japanese Yen exchange rate reflected. Identical field layout to the Mkf Index Message. *)
    Record t := {
      index_id : list byte;
      isin : list byte;
      time : list byte;
      index : list byte;
      sign : list byte;
      comparison : list byte;
      trading_volume : list byte;
      trading_value : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (comparison record) = 9 /\
      Datatypes.length (trading_volume record) = 12 /\
      Datatypes.length (trading_value record) = 12 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 9 (comparison record) ++
      encode_bytes 12 (trading_volume record) ++
      encode_bytes 12 (trading_value record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (index_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (index_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (sign_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (comparison_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (trading_volume_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (trading_value_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (filler_4_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| index_id := index_id_value; isin := isin_value; time := time_value; index := index_value; sign := sign_value; comparison := comparison_value; trading_volume := trading_volume_value; trading_value := trading_value_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
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

  End MkfIndexJpyMessage.

  Module WisefnIndexMessage.

    (** WISEfn equity index real-time message. Identical field layout to the Mkf Index Message. *)
    Record t := {
      index_id : list byte;
      isin : list byte;
      time : list byte;
      index : list byte;
      sign : list byte;
      comparison : list byte;
      trading_volume : list byte;
      trading_value : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (comparison record) = 9 /\
      Datatypes.length (trading_volume record) = 12 /\
      Datatypes.length (trading_value record) = 12 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 9 (comparison record) ++
      encode_bytes 12 (trading_volume record) ++
      encode_bytes 12 (trading_value record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (index_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (index_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (sign_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (comparison_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (trading_volume_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (trading_value_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (filler_4_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| index_id := index_id_value; isin := isin_value; time := time_value; index := index_value; sign := sign_value; comparison := comparison_value; trading_volume := trading_volume_value; trading_value := trading_value_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
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

  End WisefnIndexMessage.

  Module KisIndexMessage.

    (** KIS equity index real-time message. Identical field layout to the Mkf Index Message. *)
    Record t := {
      index_id : list byte;
      isin : list byte;
      time : list byte;
      index : list byte;
      sign : list byte;
      comparison : list byte;
      trading_volume : list byte;
      trading_value : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (index record) = 9 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (comparison record) = 9 /\
      Datatypes.length (trading_volume record) = 12 /\
      Datatypes.length (trading_value record) = 12 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (index_id record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 9 (index record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 9 (comparison record) ++
      encode_bytes 12 (trading_volume record) ++
      encode_bytes 12 (trading_value record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (index_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (index_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (sign_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (comparison_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (trading_volume_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (trading_value_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (filler_4_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| index_id := index_id_value; isin := isin_value; time := time_value; index := index_value; sign := sign_value; comparison := comparison_value; trading_volume := trading_volume_value; trading_value := trading_value_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
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

  End KisIndexMessage.

  Module MkfBondIndexMessage.

    (** MKF Bond Index real-time message. Carries total profit / clean price / market price / call and zero re-investment indices, futures basis price, duration, convexity, and YTM for one bond index identifier. *)
    Record t := {
      filler_4 : list byte;
      index_id : list byte;
      standard_date : list byte;
      standard_time : list byte;
      total_profit_index : list byte;
      clean_price_index : list byte;
      market_price_index : list byte;
      call_re_investment_index : list byte;
      zero_re_investment_index : list byte;
      futures_basis_price : list byte;
      average_duration_nullable : list byte;
      average_convexity : list byte;
      average_ytm : list byte;
      average_forward_ytm : list byte;
      filler_1 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (filler_4 record) = 4 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (standard_date record) = 8 /\
      Datatypes.length (standard_time record) = 6 /\
      Datatypes.length (total_profit_index record) = 10 /\
      Datatypes.length (clean_price_index record) = 10 /\
      Datatypes.length (market_price_index record) = 10 /\
      Datatypes.length (call_re_investment_index record) = 10 /\
      Datatypes.length (zero_re_investment_index record) = 10 /\
      Datatypes.length (futures_basis_price record) = 9 /\
      Datatypes.length (average_duration_nullable record) = 6 /\
      Datatypes.length (average_convexity record) = 6 /\
      Datatypes.length (average_ytm record) = 6 /\
      Datatypes.length (average_forward_ytm record) = 6 /\
      Datatypes.length (filler_1 record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (filler_4 record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 8 (standard_date record) ++
      encode_bytes 6 (standard_time record) ++
      encode_bytes 10 (total_profit_index record) ++
      encode_bytes 10 (clean_price_index record) ++
      encode_bytes 10 (market_price_index record) ++
      encode_bytes 10 (call_re_investment_index record) ++
      encode_bytes 10 (zero_re_investment_index record) ++
      encode_bytes 9 (futures_basis_price record) ++
      encode_bytes 6 (average_duration_nullable record) ++
      encode_bytes 6 (average_convexity record) ++
      encode_bytes 6 (average_ytm record) ++
      encode_bytes 6 (average_forward_ytm record) ++
      encode_bytes 1 (filler_1 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (filler_4_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (index_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (standard_date_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (standard_time_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (total_profit_index_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (clean_price_index_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (market_price_index_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (call_re_investment_index_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (zero_re_investment_index_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (futures_basis_price_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (average_duration_nullable_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (average_convexity_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (average_ytm_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (average_forward_ytm_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (filler_1_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| filler_4 := filler_4_value; index_id := index_id_value; standard_date := standard_date_value; standard_time := standard_time_value; total_profit_index := total_profit_index_value; clean_price_index := clean_price_index_value; market_price_index := market_price_index_value; call_re_investment_index := call_re_investment_index_value; zero_re_investment_index := zero_re_investment_index_value; futures_basis_price := futures_basis_price_value; average_duration_nullable := average_duration_nullable_value; average_convexity := average_convexity_value; average_ytm := average_ytm_value; average_forward_ytm := average_forward_ytm_value; filler_1 := filler_1_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
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

  End MkfBondIndexMessage.

  Module KisBondIndexMessage.

    (** KIS Bond Index real-time message. Identical field layout to the Mkf Bond Index Message. *)
    Record t := {
      filler_4 : list byte;
      index_id : list byte;
      standard_date : list byte;
      standard_time : list byte;
      total_profit_index : list byte;
      clean_price_index : list byte;
      market_price_index : list byte;
      call_re_investment_index : list byte;
      zero_re_investment_index : list byte;
      futures_basis_price : list byte;
      average_duration : list byte;
      average_convexity : list byte;
      average_ytm : list byte;
      average_forward_ytm : list byte;
      filler_1 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (filler_4 record) = 4 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (standard_date record) = 8 /\
      Datatypes.length (standard_time record) = 6 /\
      Datatypes.length (total_profit_index record) = 10 /\
      Datatypes.length (clean_price_index record) = 10 /\
      Datatypes.length (market_price_index record) = 10 /\
      Datatypes.length (call_re_investment_index record) = 10 /\
      Datatypes.length (zero_re_investment_index record) = 10 /\
      Datatypes.length (futures_basis_price record) = 9 /\
      Datatypes.length (average_duration record) = 6 /\
      Datatypes.length (average_convexity record) = 6 /\
      Datatypes.length (average_ytm record) = 6 /\
      Datatypes.length (average_forward_ytm record) = 6 /\
      Datatypes.length (filler_1 record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (filler_4 record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 8 (standard_date record) ++
      encode_bytes 6 (standard_time record) ++
      encode_bytes 10 (total_profit_index record) ++
      encode_bytes 10 (clean_price_index record) ++
      encode_bytes 10 (market_price_index record) ++
      encode_bytes 10 (call_re_investment_index record) ++
      encode_bytes 10 (zero_re_investment_index record) ++
      encode_bytes 9 (futures_basis_price record) ++
      encode_bytes 6 (average_duration record) ++
      encode_bytes 6 (average_convexity record) ++
      encode_bytes 6 (average_ytm record) ++
      encode_bytes 6 (average_forward_ytm record) ++
      encode_bytes 1 (filler_1 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (filler_4_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (index_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (standard_date_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (standard_time_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (total_profit_index_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (clean_price_index_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (market_price_index_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (call_re_investment_index_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (zero_re_investment_index_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (futures_basis_price_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (average_duration_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (average_convexity_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (average_ytm_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (average_forward_ytm_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (filler_1_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| filler_4 := filler_4_value; index_id := index_id_value; standard_date := standard_date_value; standard_time := standard_time_value; total_profit_index := total_profit_index_value; clean_price_index := clean_price_index_value; market_price_index := market_price_index_value; call_re_investment_index := call_re_investment_index_value; zero_re_investment_index := zero_re_investment_index_value; futures_basis_price := futures_basis_price_value; average_duration := average_duration_value; average_convexity := average_convexity_value; average_ytm := average_ytm_value; average_forward_ytm := average_forward_ytm_value; filler_1 := filler_1_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
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

  End KisBondIndexMessage.

  Module KebiBondIndexMessage.

    (** KEBI Bond Index real-time message. Identical field layout to the Mkf Bond Index Message. *)
    Record t := {
      filler_4 : list byte;
      index_id : list byte;
      standard_date : list byte;
      standard_time : list byte;
      total_profit_index : list byte;
      clean_price_index : list byte;
      market_price_index : list byte;
      call_re_investment_index : list byte;
      zero_re_investment_index : list byte;
      futures_basis_price : list byte;
      average_duration_nullable : list byte;
      average_convexity : list byte;
      average_ytm : list byte;
      average_forward_ytm : list byte;
      filler_1 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (filler_4 record) = 4 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (standard_date record) = 8 /\
      Datatypes.length (standard_time record) = 6 /\
      Datatypes.length (total_profit_index record) = 10 /\
      Datatypes.length (clean_price_index record) = 10 /\
      Datatypes.length (market_price_index record) = 10 /\
      Datatypes.length (call_re_investment_index record) = 10 /\
      Datatypes.length (zero_re_investment_index record) = 10 /\
      Datatypes.length (futures_basis_price record) = 9 /\
      Datatypes.length (average_duration_nullable record) = 6 /\
      Datatypes.length (average_convexity record) = 6 /\
      Datatypes.length (average_ytm record) = 6 /\
      Datatypes.length (average_forward_ytm record) = 6 /\
      Datatypes.length (filler_1 record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (filler_4 record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 8 (standard_date record) ++
      encode_bytes 6 (standard_time record) ++
      encode_bytes 10 (total_profit_index record) ++
      encode_bytes 10 (clean_price_index record) ++
      encode_bytes 10 (market_price_index record) ++
      encode_bytes 10 (call_re_investment_index record) ++
      encode_bytes 10 (zero_re_investment_index record) ++
      encode_bytes 9 (futures_basis_price record) ++
      encode_bytes 6 (average_duration_nullable record) ++
      encode_bytes 6 (average_convexity record) ++
      encode_bytes 6 (average_ytm record) ++
      encode_bytes 6 (average_forward_ytm record) ++
      encode_bytes 1 (filler_1 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (filler_4_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (index_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (standard_date_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (standard_time_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (total_profit_index_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (clean_price_index_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (market_price_index_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (call_re_investment_index_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (zero_re_investment_index_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (futures_basis_price_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (average_duration_nullable_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (average_convexity_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (average_ytm_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (average_forward_ytm_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (filler_1_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| filler_4 := filler_4_value; index_id := index_id_value; standard_date := standard_date_value; standard_time := standard_time_value; total_profit_index := total_profit_index_value; clean_price_index := clean_price_index_value; market_price_index := market_price_index_value; call_re_investment_index := call_re_investment_index_value; zero_re_investment_index := zero_re_investment_index_value; futures_basis_price := futures_basis_price_value; average_duration_nullable := average_duration_nullable_value; average_convexity := average_convexity_value; average_ytm := average_ytm_value; average_forward_ytm := average_forward_ytm_value; filler_1 := filler_1_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
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

  End KebiBondIndexMessage.

  Module KabiBondIndexMessage.

    (** KABI Bond Index real-time message. Same field layout as the Mkf Bond Index Message; KABI uses standard 100 rather than 10,000 for the various indices. *)
    Record t := {
      filler_4 : list byte;
      index_id : list byte;
      standard_date : list byte;
      standard_time : list byte;
      total_profit_index : list byte;
      clean_price_index : list byte;
      market_price_index : list byte;
      call_re_investment_index : list byte;
      zero_re_investment_index : list byte;
      futures_basis_price_nullable : list byte;
      average_duration : list byte;
      average_convexity : list byte;
      average_ytm : list byte;
      average_forward_ytm_nullable : list byte;
      filler_1 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (filler_4 record) = 4 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (standard_date record) = 8 /\
      Datatypes.length (standard_time record) = 6 /\
      Datatypes.length (total_profit_index record) = 10 /\
      Datatypes.length (clean_price_index record) = 10 /\
      Datatypes.length (market_price_index record) = 10 /\
      Datatypes.length (call_re_investment_index record) = 10 /\
      Datatypes.length (zero_re_investment_index record) = 10 /\
      Datatypes.length (futures_basis_price_nullable record) = 9 /\
      Datatypes.length (average_duration record) = 6 /\
      Datatypes.length (average_convexity record) = 6 /\
      Datatypes.length (average_ytm record) = 6 /\
      Datatypes.length (average_forward_ytm_nullable record) = 6 /\
      Datatypes.length (filler_1 record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (filler_4 record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 8 (standard_date record) ++
      encode_bytes 6 (standard_time record) ++
      encode_bytes 10 (total_profit_index record) ++
      encode_bytes 10 (clean_price_index record) ++
      encode_bytes 10 (market_price_index record) ++
      encode_bytes 10 (call_re_investment_index record) ++
      encode_bytes 10 (zero_re_investment_index record) ++
      encode_bytes 9 (futures_basis_price_nullable record) ++
      encode_bytes 6 (average_duration record) ++
      encode_bytes 6 (average_convexity record) ++
      encode_bytes 6 (average_ytm record) ++
      encode_bytes 6 (average_forward_ytm_nullable record) ++
      encode_bytes 1 (filler_1 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (filler_4_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (index_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (standard_date_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (standard_time_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (total_profit_index_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (clean_price_index_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (market_price_index_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (call_re_investment_index_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (zero_re_investment_index_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (futures_basis_price_nullable_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (average_duration_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (average_convexity_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (average_ytm_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (average_forward_ytm_nullable_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (filler_1_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| filler_4 := filler_4_value; index_id := index_id_value; standard_date := standard_date_value; standard_time := standard_time_value; total_profit_index := total_profit_index_value; clean_price_index := clean_price_index_value; market_price_index := market_price_index_value; call_re_investment_index := call_re_investment_index_value; zero_re_investment_index := zero_re_investment_index_value; futures_basis_price_nullable := futures_basis_price_nullable_value; average_duration := average_duration_value; average_convexity := average_convexity_value; average_ytm := average_ytm_value; average_forward_ytm_nullable := average_forward_ytm_nullable_value; filler_1 := filler_1_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
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

  End KabiBondIndexMessage.

  Module NicepniBondIndexMessage.

    (** NicePNI Bond Index real-time message. Identical field layout to the Mkf Bond Index Message. *)
    Record t := {
      filler_4 : list byte;
      index_id : list byte;
      standard_date : list byte;
      standard_time : list byte;
      total_profit_index : list byte;
      clean_price_index : list byte;
      market_price_index : list byte;
      call_re_investment_index : list byte;
      zero_re_investment_index : list byte;
      futures_basis_price : list byte;
      average_duration_nullable : list byte;
      average_convexity : list byte;
      average_ytm : list byte;
      average_forward_ytm : list byte;
      filler_1 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (filler_4 record) = 4 /\
      Datatypes.length (index_id record) = 6 /\
      Datatypes.length (standard_date record) = 8 /\
      Datatypes.length (standard_time record) = 6 /\
      Datatypes.length (total_profit_index record) = 10 /\
      Datatypes.length (clean_price_index record) = 10 /\
      Datatypes.length (market_price_index record) = 10 /\
      Datatypes.length (call_re_investment_index record) = 10 /\
      Datatypes.length (zero_re_investment_index record) = 10 /\
      Datatypes.length (futures_basis_price record) = 9 /\
      Datatypes.length (average_duration_nullable record) = 6 /\
      Datatypes.length (average_convexity record) = 6 /\
      Datatypes.length (average_ytm record) = 6 /\
      Datatypes.length (average_forward_ytm record) = 6 /\
      Datatypes.length (filler_1 record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (filler_4 record) ++
      encode_bytes 6 (index_id record) ++
      encode_bytes 8 (standard_date record) ++
      encode_bytes 6 (standard_time record) ++
      encode_bytes 10 (total_profit_index record) ++
      encode_bytes 10 (clean_price_index record) ++
      encode_bytes 10 (market_price_index record) ++
      encode_bytes 10 (call_re_investment_index record) ++
      encode_bytes 10 (zero_re_investment_index record) ++
      encode_bytes 9 (futures_basis_price record) ++
      encode_bytes 6 (average_duration_nullable record) ++
      encode_bytes 6 (average_convexity record) ++
      encode_bytes 6 (average_ytm record) ++
      encode_bytes 6 (average_forward_ytm record) ++
      encode_bytes 1 (filler_1 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (filler_4_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (index_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (standard_date_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (standard_time_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (total_profit_index_value, bytes) =>
                          match decode_bytes 10 bytes with
                          | None => None
                          | Some (clean_price_index_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (market_price_index_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (call_re_investment_index_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (zero_re_investment_index_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (futures_basis_price_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (average_duration_nullable_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (average_convexity_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (average_ytm_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (average_forward_ytm_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (filler_1_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (end_keyword_value, bytes) =>
                                                                      Some ({| filler_4 := filler_4_value; index_id := index_id_value; standard_date := standard_date_value; standard_time := standard_time_value; total_profit_index := total_profit_index_value; clean_price_index := clean_price_index_value; market_price_index := market_price_index_value; call_re_investment_index := call_re_investment_index_value; zero_re_investment_index := zero_re_investment_index_value; futures_basis_price := futures_basis_price_value; average_duration_nullable := average_duration_nullable_value; average_convexity := average_convexity_value; average_ytm := average_ytm_value; average_forward_ytm := average_forward_ytm_value; filler_1 := filler_1_value; end_keyword := end_keyword_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 109.
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

  End NicepniBondIndexMessage.

  Module DomesticEtfInavMessage.

    (** Domestic ETF intraday NAV (1-second interval). Carries previous-day and during-market/final NAV per ETF ISIN. *)
    Record t := {
      isin : list byte;
      time : list byte;
      previous_nav : list byte;
      during_marketfinal_nav : list byte;
      filler_28 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (previous_nav record) = 9 /\
      Datatypes.length (during_marketfinal_nav record) = 9 /\
      Datatypes.length (filler_28 record) = 28 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 9 (previous_nav record) ++
      encode_bytes 9 (during_marketfinal_nav record) ++
      encode_bytes 28 (filler_28 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (previous_nav_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (during_marketfinal_nav_value, bytes) =>
                      match decode_bytes 28 bytes with
                      | None => None
                      | Some (filler_28_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| isin := isin_value; time := time_value; previous_nav := previous_nav_value; during_marketfinal_nav := during_marketfinal_nav_value; filler_28 := filler_28_value; end_keyword := end_keyword_value |}, bytes)
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

  End DomesticEtfInavMessage.

  Module DomesticEtfEstimatedInavMessage.

    (** Domestic ETF Estimated iNAV. Carries previous-day and during-market/final estimated NAV. *)
    Record t := {
      isin : list byte;
      time : list byte;
      previous_nav : list byte;
      during_marketfinal_market_nav : list byte;
      filler_8 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (previous_nav record) = 9 /\
      Datatypes.length (during_marketfinal_market_nav record) = 9 /\
      Datatypes.length (filler_8 record) = 8 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 9 (previous_nav record) ++
      encode_bytes 9 (during_marketfinal_market_nav record) ++
      encode_bytes 8 (filler_8 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (previous_nav_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (during_marketfinal_market_nav_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (filler_8_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| isin := isin_value; time := time_value; previous_nav := previous_nav_value; during_marketfinal_market_nav := during_marketfinal_market_nav_value; filler_8 := filler_8_value; end_keyword := end_keyword_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
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

  End DomesticEtfEstimatedInavMessage.

  Module GlobalEtfInavMessage.

    (** Global ETF intraday NAV per ETF ISIN. *)
    Record t := {
      isin : list byte;
      time : list byte;
      previous_nav : list byte;
      during_marketfinal_nav : list byte;
      filler_28 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (previous_nav record) = 9 /\
      Datatypes.length (during_marketfinal_nav record) = 9 /\
      Datatypes.length (filler_28 record) = 28 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 9 (previous_nav record) ++
      encode_bytes 9 (during_marketfinal_nav record) ++
      encode_bytes 28 (filler_28 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (previous_nav_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (during_marketfinal_nav_value, bytes) =>
                      match decode_bytes 28 bytes with
                      | None => None
                      | Some (filler_28_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| isin := isin_value; time := time_value; previous_nav := previous_nav_value; during_marketfinal_nav := during_marketfinal_nav_value; filler_28 := filler_28_value; end_keyword := end_keyword_value |}, bytes)
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

  End GlobalEtfInavMessage.

  Module EtfTrackingErrorMessage.

    (** ETF tracking error and signed disparate ratio per ETF. *)
    Record t := {
      isin : list byte;
      seq_number : list byte;
      date : list byte;
      tracking_error : list byte;
      disparate_ratio_sign : list byte;
      disparate_ratio : list byte;
      filler_7 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (seq_number record) = 8 /\
      Datatypes.length (date record) = 8 /\
      Datatypes.length (tracking_error record) = 9 /\
      Datatypes.length (disparate_ratio_sign record) = 1 /\
      Datatypes.length (disparate_ratio record) = 9 /\
      Datatypes.length (filler_7 record) = 7 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (seq_number record) ++
      encode_bytes 8 (date record) ++
      encode_bytes 9 (tracking_error record) ++
      encode_bytes 1 (disparate_ratio_sign record) ++
      encode_bytes 9 (disparate_ratio record) ++
      encode_bytes 7 (filler_7 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (seq_number_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (date_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (tracking_error_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (disparate_ratio_sign_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (disparate_ratio_value, bytes) =>
                              match decode_bytes 7 bytes with
                              | None => None
                              | Some (filler_7_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| isin := isin_value; seq_number := seq_number_value; date := date_value; tracking_error := tracking_error_value; disparate_ratio_sign := disparate_ratio_sign_value; disparate_ratio := disparate_ratio_value; filler_7 := filler_7_value; end_keyword := end_keyword_value |}, bytes)
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

  End EtfTrackingErrorMessage.

  Module GlobalEtfTrackingErrorMessage.

    (** Global ETF tracking error and signed disparate ratio. *)
    Record t := {
      isin : list byte;
      seq_number : list byte;
      date : list byte;
      tracking_error : list byte;
      disparate_ratio_sign : list byte;
      disparate_ratio : list byte;
      filler_7 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (seq_number record) = 8 /\
      Datatypes.length (date record) = 8 /\
      Datatypes.length (tracking_error record) = 9 /\
      Datatypes.length (disparate_ratio_sign record) = 1 /\
      Datatypes.length (disparate_ratio record) = 9 /\
      Datatypes.length (filler_7 record) = 7 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (seq_number record) ++
      encode_bytes 8 (date record) ++
      encode_bytes 9 (tracking_error record) ++
      encode_bytes 1 (disparate_ratio_sign record) ++
      encode_bytes 9 (disparate_ratio record) ++
      encode_bytes 7 (filler_7 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (seq_number_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (date_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (tracking_error_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (disparate_ratio_sign_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (disparate_ratio_value, bytes) =>
                              match decode_bytes 7 bytes with
                              | None => None
                              | Some (filler_7_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| isin := isin_value; seq_number := seq_number_value; date := date_value; tracking_error := tracking_error_value; disparate_ratio_sign := disparate_ratio_sign_value; disparate_ratio := disparate_ratio_value; filler_7 := filler_7_value; end_keyword := end_keyword_value |}, bytes)
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

  End GlobalEtfTrackingErrorMessage.

  Module EtpPdfMessage.

    (** ETP Portfolio Deposit File. One record per composition issue: unit share, market type, issue name, par value, appraised value, profit distribution basis date. *)
    Record t := {
      isin : list byte;
      data_seq_number : list byte;
      date : list byte;
      office_consignment_companys_registration_number : list byte;
      composition_issue_number : list byte;
      composition_issue_code : list byte;
      c_u_unit_share_number_of_contract_k_r_w_cash_u_s_d_cash_converted_amount_k_r_w : list byte;
      composition_issue_market_type : list byte;
      composition_issue_name : list byte;
      par_value_amount_cash_amount_converted_amount_krw : list byte;
      profit_distribution_basis_date : list byte;
      appraised_value : list byte;
      filler_4 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_seq_number record) = 8 /\
      Datatypes.length (date record) = 8 /\
      Datatypes.length (office_consignment_companys_registration_number record) = 3 /\
      Datatypes.length (composition_issue_number record) = 4 /\
      Datatypes.length (composition_issue_code record) = 12 /\
      Datatypes.length (c_u_unit_share_number_of_contract_k_r_w_cash_u_s_d_cash_converted_amount_k_r_w record) = 18 /\
      Datatypes.length (composition_issue_market_type record) = 1 /\
      Datatypes.length (composition_issue_name record) = 40 /\
      Datatypes.length (par_value_amount_cash_amount_converted_amount_krw record) = 18 /\
      Datatypes.length (profit_distribution_basis_date record) = 8 /\
      Datatypes.length (appraised_value record) = 18 /\
      Datatypes.length (filler_4 record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (data_seq_number record) ++
      encode_bytes 8 (date record) ++
      encode_bytes 3 (office_consignment_companys_registration_number record) ++
      encode_bytes 4 (composition_issue_number record) ++
      encode_bytes 12 (composition_issue_code record) ++
      encode_bytes 18 (c_u_unit_share_number_of_contract_k_r_w_cash_u_s_d_cash_converted_amount_k_r_w record) ++
      encode_bytes 1 (composition_issue_market_type record) ++
      encode_bytes 40 (composition_issue_name record) ++
      encode_bytes 18 (par_value_amount_cash_amount_converted_amount_krw record) ++
      encode_bytes 8 (profit_distribution_basis_date record) ++
      encode_bytes 18 (appraised_value record) ++
      encode_bytes 4 (filler_4 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (data_seq_number_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (date_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (office_consignment_companys_registration_number_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (composition_issue_number_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (composition_issue_code_value, bytes) =>
                              match decode_bytes 18 bytes with
                              | None => None
                              | Some (c_u_unit_share_number_of_contract_k_r_w_cash_u_s_d_cash_converted_amount_k_r_w_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (composition_issue_market_type_value, bytes) =>
                                      match decode_bytes 40 bytes with
                                      | None => None
                                      | Some (composition_issue_name_value, bytes) =>
                                          match decode_bytes 18 bytes with
                                          | None => None
                                          | Some (par_value_amount_cash_amount_converted_amount_krw_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (profit_distribution_basis_date_value, bytes) =>
                                                  match decode_bytes 18 bytes with
                                                  | None => None
                                                  | Some (appraised_value_value, bytes) =>
                                                      match decode_bytes 4 bytes with
                                                      | None => None
                                                      | Some (filler_4_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (end_keyword_value, bytes) =>
                                                              Some ({| isin := isin_value; data_seq_number := data_seq_number_value; date := date_value; office_consignment_companys_registration_number := office_consignment_companys_registration_number_value; composition_issue_number := composition_issue_number_value; composition_issue_code := composition_issue_code_value; c_u_unit_share_number_of_contract_k_r_w_cash_u_s_d_cash_converted_amount_k_r_w := c_u_unit_share_number_of_contract_k_r_w_cash_u_s_d_cash_converted_amount_k_r_w_value; composition_issue_market_type := composition_issue_market_type_value; composition_issue_name := composition_issue_name_value; par_value_amount_cash_amount_converted_amount_krw := par_value_amount_cash_amount_converted_amount_krw_value; profit_distribution_basis_date := profit_distribution_basis_date_value; appraised_value := appraised_value_value; filler_4 := filler_4_value; end_keyword := end_keyword_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 155.
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

  End EtpPdfMessage.

  Module EtpOperatorInformationMessage.

    (** ETP/BDC operator information. Office consignment company, operator code, and abbreviated names in Korean and English. *)
    Record t := {
      isin : list byte;
      seq_number : list byte;
      office_consignment_companys_registration_number : list byte;
      operator_code : list byte;
      operator_abbreviated_name_korean : list byte;
      operator_abbreviated_name_english : list byte;
      filler_5 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (seq_number record) = 8 /\
      Datatypes.length (office_consignment_companys_registration_number record) = 3 /\
      Datatypes.length (operator_code record) = 6 /\
      Datatypes.length (operator_abbreviated_name_korean record) = 50 /\
      Datatypes.length (operator_abbreviated_name_english record) = 40 /\
      Datatypes.length (filler_5 record) = 5 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (seq_number record) ++
      encode_bytes 3 (office_consignment_companys_registration_number record) ++
      encode_bytes 6 (operator_code record) ++
      encode_bytes 50 (operator_abbreviated_name_korean record) ++
      encode_bytes 40 (operator_abbreviated_name_english record) ++
      encode_bytes 5 (filler_5 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (seq_number_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (office_consignment_companys_registration_number_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (operator_code_value, bytes) =>
                      match decode_bytes 50 bytes with
                      | None => None
                      | Some (operator_abbreviated_name_korean_value, bytes) =>
                          match decode_bytes 40 bytes with
                          | None => None
                          | Some (operator_abbreviated_name_english_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (filler_5_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| isin := isin_value; seq_number := seq_number_value; office_consignment_companys_registration_number := office_consignment_companys_registration_number_value; operator_code := operator_code_value; operator_abbreviated_name_korean := operator_abbreviated_name_korean_value; operator_abbreviated_name_english := operator_abbreviated_name_english_value; filler_5 := filler_5_value; end_keyword := end_keyword_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 125.
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

  End EtpOperatorInformationMessage.

  Module EtpTransferAgentBatchMessage.

    (** ETP/BDC transfer agent batch data. *)
    Record t := {
      isin : list byte;
      data_seq_number : list byte;
      filler_10 : list byte;
      etf_flow_net_asset_total_amount : list byte;
      etf_foreign_net_asset_value_amount : list byte;
      etf_net_asset_value_amount : list byte;
      etf_foreign_flow_net_asset_total_amount : list byte;
      etf_foreign_net_asset_total : list byte;
      etf_foreign_final_net_asset_value : list byte;
      etf_cu_quantity : list byte;
      previous_days_tax_base_nav : list byte;
      previous_days_tax_base_nav_before_dividend : list byte;
      previous_days_cash_dividend_amount : list byte;
      tax_base_nav_as_of_the_day_before_the_previous_day : list byte;
      previous_days_non_taxable_base_price_for_overseas_stocks : list byte;
      previous_days_non_taxable_base_price_before_dividend_for_overseas_stocks : list byte;
      day_before_previous_days_non_taxable_base_price_for_overseas_stocks : list byte;
      number_of_free_floating_etf_shares : list byte;
      filler_46 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_seq_number record) = 8 /\
      Datatypes.length (filler_10 record) = 10 /\
      Datatypes.length (etf_flow_net_asset_total_amount record) = 15 /\
      Datatypes.length (etf_foreign_net_asset_value_amount record) = 15 /\
      Datatypes.length (etf_net_asset_value_amount record) = 9 /\
      Datatypes.length (etf_foreign_flow_net_asset_total_amount record) = 15 /\
      Datatypes.length (etf_foreign_net_asset_total record) = 15 /\
      Datatypes.length (etf_foreign_final_net_asset_value record) = 9 /\
      Datatypes.length (etf_cu_quantity record) = 8 /\
      Datatypes.length (previous_days_tax_base_nav record) = 9 /\
      Datatypes.length (previous_days_tax_base_nav_before_dividend record) = 9 /\
      Datatypes.length (previous_days_cash_dividend_amount record) = 12 /\
      Datatypes.length (tax_base_nav_as_of_the_day_before_the_previous_day record) = 9 /\
      Datatypes.length (previous_days_non_taxable_base_price_for_overseas_stocks record) = 9 /\
      Datatypes.length (previous_days_non_taxable_base_price_before_dividend_for_overseas_stocks record) = 9 /\
      Datatypes.length (day_before_previous_days_non_taxable_base_price_for_overseas_stocks record) = 9 /\
      Datatypes.length (number_of_free_floating_etf_shares record) = 16 /\
      Datatypes.length (filler_46 record) = 46 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (data_seq_number record) ++
      encode_bytes 10 (filler_10 record) ++
      encode_bytes 15 (etf_flow_net_asset_total_amount record) ++
      encode_bytes 15 (etf_foreign_net_asset_value_amount record) ++
      encode_bytes 9 (etf_net_asset_value_amount record) ++
      encode_bytes 15 (etf_foreign_flow_net_asset_total_amount record) ++
      encode_bytes 15 (etf_foreign_net_asset_total record) ++
      encode_bytes 9 (etf_foreign_final_net_asset_value record) ++
      encode_bytes 8 (etf_cu_quantity record) ++
      encode_bytes 9 (previous_days_tax_base_nav record) ++
      encode_bytes 9 (previous_days_tax_base_nav_before_dividend record) ++
      encode_bytes 12 (previous_days_cash_dividend_amount record) ++
      encode_bytes 9 (tax_base_nav_as_of_the_day_before_the_previous_day record) ++
      encode_bytes 9 (previous_days_non_taxable_base_price_for_overseas_stocks record) ++
      encode_bytes 9 (previous_days_non_taxable_base_price_before_dividend_for_overseas_stocks record) ++
      encode_bytes 9 (day_before_previous_days_non_taxable_base_price_for_overseas_stocks record) ++
      encode_bytes 16 (number_of_free_floating_etf_shares record) ++
      encode_bytes 46 (filler_46 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (data_seq_number_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (filler_10_value, bytes) =>
                  match decode_bytes 15 bytes with
                  | None => None
                  | Some (etf_flow_net_asset_total_amount_value, bytes) =>
                      match decode_bytes 15 bytes with
                      | None => None
                      | Some (etf_foreign_net_asset_value_amount_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (etf_net_asset_value_amount_value, bytes) =>
                              match decode_bytes 15 bytes with
                              | None => None
                              | Some (etf_foreign_flow_net_asset_total_amount_value, bytes) =>
                                  match decode_bytes 15 bytes with
                                  | None => None
                                  | Some (etf_foreign_net_asset_total_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (etf_foreign_final_net_asset_value_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (etf_cu_quantity_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (previous_days_tax_base_nav_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (previous_days_tax_base_nav_before_dividend_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (previous_days_cash_dividend_amount_value, bytes) =>
                                                          match decode_bytes 9 bytes with
                                                          | None => None
                                                          | Some (tax_base_nav_as_of_the_day_before_the_previous_day_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (previous_days_non_taxable_base_price_for_overseas_stocks_value, bytes) =>
                                                                  match decode_bytes 9 bytes with
                                                                  | None => None
                                                                  | Some (previous_days_non_taxable_base_price_before_dividend_for_overseas_stocks_value, bytes) =>
                                                                      match decode_bytes 9 bytes with
                                                                      | None => None
                                                                      | Some (day_before_previous_days_non_taxable_base_price_for_overseas_stocks_value, bytes) =>
                                                                          match decode_bytes 16 bytes with
                                                                          | None => None
                                                                          | Some (number_of_free_floating_etf_shares_value, bytes) =>
                                                                              match decode_bytes 46 bytes with
                                                                              | None => None
                                                                              | Some (filler_46_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                      Some ({| isin := isin_value; data_seq_number := data_seq_number_value; filler_10 := filler_10_value; etf_flow_net_asset_total_amount := etf_flow_net_asset_total_amount_value; etf_foreign_net_asset_value_amount := etf_foreign_net_asset_value_amount_value; etf_net_asset_value_amount := etf_net_asset_value_amount_value; etf_foreign_flow_net_asset_total_amount := etf_foreign_flow_net_asset_total_amount_value; etf_foreign_net_asset_total := etf_foreign_net_asset_total_value; etf_foreign_final_net_asset_value := etf_foreign_final_net_asset_value_value; etf_cu_quantity := etf_cu_quantity_value; previous_days_tax_base_nav := previous_days_tax_base_nav_value; previous_days_tax_base_nav_before_dividend := previous_days_tax_base_nav_before_dividend_value; previous_days_cash_dividend_amount := previous_days_cash_dividend_amount_value; tax_base_nav_as_of_the_day_before_the_previous_day := tax_base_nav_as_of_the_day_before_the_previous_day_value; previous_days_non_taxable_base_price_for_overseas_stocks := previous_days_non_taxable_base_price_for_overseas_stocks_value; previous_days_non_taxable_base_price_before_dividend_for_overseas_stocks := previous_days_non_taxable_base_price_before_dividend_for_overseas_stocks_value; day_before_previous_days_non_taxable_base_price_for_overseas_stocks := day_before_previous_days_non_taxable_base_price_for_overseas_stocks_value; number_of_free_floating_etf_shares := number_of_free_floating_etf_shares_value; filler_46 := filler_46_value; end_keyword := end_keyword_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 245.
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

  End EtpTransferAgentBatchMessage.

  Module EtfRiskAppraisementMessage.

    (** Synthetic ETF risk appraisement daily trading data. *)
    Record t := {
      isin : list byte;
      data_seq_number : list byte;
      date : list byte;
      office_consignment_companys_registration_number : list byte;
      name_of_counterparty : list byte;
      otc_derivatives_type : list byte;
      net_assets_amount : list byte;
      total_danger_exposure_amount : list byte;
      security_appraisal_amount : list byte;
      security_rate : list byte;
      risk_appraisal_amount : list byte;
      risk_appraisal_amount_rate : list byte;
      filler_38 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_seq_number record) = 8 /\
      Datatypes.length (date record) = 8 /\
      Datatypes.length (office_consignment_companys_registration_number record) = 3 /\
      Datatypes.length (name_of_counterparty record) = 50 /\
      Datatypes.length (otc_derivatives_type record) = 1 /\
      Datatypes.length (net_assets_amount record) = 15 /\
      Datatypes.length (total_danger_exposure_amount record) = 15 /\
      Datatypes.length (security_appraisal_amount record) = 15 /\
      Datatypes.length (security_rate record) = 7 /\
      Datatypes.length (risk_appraisal_amount record) = 15 /\
      Datatypes.length (risk_appraisal_amount_rate record) = 7 /\
      Datatypes.length (filler_38 record) = 38 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (data_seq_number record) ++
      encode_bytes 8 (date record) ++
      encode_bytes 3 (office_consignment_companys_registration_number record) ++
      encode_bytes 50 (name_of_counterparty record) ++
      encode_bytes 1 (otc_derivatives_type record) ++
      encode_bytes 15 (net_assets_amount record) ++
      encode_bytes 15 (total_danger_exposure_amount record) ++
      encode_bytes 15 (security_appraisal_amount record) ++
      encode_bytes 7 (security_rate record) ++
      encode_bytes 15 (risk_appraisal_amount record) ++
      encode_bytes 7 (risk_appraisal_amount_rate record) ++
      encode_bytes 38 (filler_38 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (data_seq_number_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (date_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (office_consignment_companys_registration_number_value, bytes) =>
                      match decode_bytes 50 bytes with
                      | None => None
                      | Some (name_of_counterparty_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (otc_derivatives_type_value, bytes) =>
                              match decode_bytes 15 bytes with
                              | None => None
                              | Some (net_assets_amount_value, bytes) =>
                                  match decode_bytes 15 bytes with
                                  | None => None
                                  | Some (total_danger_exposure_amount_value, bytes) =>
                                      match decode_bytes 15 bytes with
                                      | None => None
                                      | Some (security_appraisal_amount_value, bytes) =>
                                          match decode_bytes 7 bytes with
                                          | None => None
                                          | Some (security_rate_value, bytes) =>
                                              match decode_bytes 15 bytes with
                                              | None => None
                                              | Some (risk_appraisal_amount_value, bytes) =>
                                                  match decode_bytes 7 bytes with
                                                  | None => None
                                                  | Some (risk_appraisal_amount_rate_value, bytes) =>
                                                      match decode_bytes 38 bytes with
                                                      | None => None
                                                      | Some (filler_38_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (end_keyword_value, bytes) =>
                                                              Some ({| isin := isin_value; data_seq_number := data_seq_number_value; date := date_value; office_consignment_companys_registration_number := office_consignment_companys_registration_number_value; name_of_counterparty := name_of_counterparty_value; otc_derivatives_type := otc_derivatives_type_value; net_assets_amount := net_assets_amount_value; total_danger_exposure_amount := total_danger_exposure_amount_value; security_appraisal_amount := security_appraisal_amount_value; security_rate := security_rate_value; risk_appraisal_amount := risk_appraisal_amount_value; risk_appraisal_amount_rate := risk_appraisal_amount_rate_value; filler_38 := filler_38_value; end_keyword := end_keyword_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 195.
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

  End EtfRiskAppraisementMessage.

  Module SyntheticEtfConstituentsMessage.

    (** Synthetic ETF basic index composition constituents. *)
    Record t := {
      isin : list byte;
      data_seq_number : list byte;
      date : list byte;
      office_consignment_companys_registration_number : list byte;
      composition_constituents_number : list byte;
      composition_constituents_code : list byte;
      composition_constituents_name : list byte;
      composition_ratio : list byte;
      filler_60 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (data_seq_number record) = 8 /\
      Datatypes.length (date record) = 8 /\
      Datatypes.length (office_consignment_companys_registration_number record) = 3 /\
      Datatypes.length (composition_constituents_number record) = 4 /\
      Datatypes.length (composition_constituents_code record) = 12 /\
      Datatypes.length (composition_constituents_name record) = 80 /\
      Datatypes.length (composition_ratio record) = 7 /\
      Datatypes.length (filler_60 record) = 60 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (data_seq_number record) ++
      encode_bytes 8 (date record) ++
      encode_bytes 3 (office_consignment_companys_registration_number record) ++
      encode_bytes 4 (composition_constituents_number record) ++
      encode_bytes 12 (composition_constituents_code record) ++
      encode_bytes 80 (composition_constituents_name record) ++
      encode_bytes 7 (composition_ratio record) ++
      encode_bytes 60 (filler_60 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (data_seq_number_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (date_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (office_consignment_companys_registration_number_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (composition_constituents_number_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (composition_constituents_code_value, bytes) =>
                              match decode_bytes 80 bytes with
                              | None => None
                              | Some (composition_constituents_name_value, bytes) =>
                                  match decode_bytes 7 bytes with
                                  | None => None
                                  | Some (composition_ratio_value, bytes) =>
                                      match decode_bytes 60 bytes with
                                      | None => None
                                      | Some (filler_60_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| isin := isin_value; data_seq_number := data_seq_number_value; date := date_value; office_consignment_companys_registration_number := office_consignment_companys_registration_number_value; composition_constituents_number := composition_constituents_number_value; composition_constituents_code := composition_constituents_code_value; composition_constituents_name := composition_constituents_name_value; composition_ratio := composition_ratio_value; filler_60 := filler_60_value; end_keyword := end_keyword_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 195.
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

  End SyntheticEtfConstituentsMessage.

  Module ElwInvestmentIndicatorSensitivityMessage.

    (** ELW Investment Indicator Sensitivity. Theoretical warrant price plus signed Delta/Gamma/Theta/Vega/Rho sensitivities, intrinsic volatility, and prerequisite cost. *)
    Record t := {
      isin : list byte;
      time : list byte;
      theoretical_warrant_price : list byte;
      sensitivity_delta_sign : list byte;
      sensitivity_delta : list byte;
      sensitivity_gamma_sign : list byte;
      sensitivity_gamma : list byte;
      sensitivity_theta_sign : list byte;
      sensitivity_theta : list byte;
      sensitivity_vega_sign : list byte;
      sensitivity_vega : list byte;
      sensitivity_rho_sign : list byte;
      sensitivity_rho : list byte;
      intrinsic_volatility : list byte;
      prerequisite_cost : list byte;
      filler_6 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (time record) = 6 /\
      Datatypes.length (theoretical_warrant_price record) = 10 /\
      Datatypes.length (sensitivity_delta_sign record) = 1 /\
      Datatypes.length (sensitivity_delta record) = 7 /\
      Datatypes.length (sensitivity_gamma_sign record) = 1 /\
      Datatypes.length (sensitivity_gamma record) = 7 /\
      Datatypes.length (sensitivity_theta_sign record) = 1 /\
      Datatypes.length (sensitivity_theta record) = 12 /\
      Datatypes.length (sensitivity_vega_sign record) = 1 /\
      Datatypes.length (sensitivity_vega record) = 12 /\
      Datatypes.length (sensitivity_rho_sign record) = 1 /\
      Datatypes.length (sensitivity_rho record) = 12 /\
      Datatypes.length (intrinsic_volatility record) = 5 /\
      Datatypes.length (prerequisite_cost record) = 10 /\
      Datatypes.length (filler_6 record) = 6 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (time record) ++
      encode_bytes 10 (theoretical_warrant_price record) ++
      encode_bytes 1 (sensitivity_delta_sign record) ++
      encode_bytes 7 (sensitivity_delta record) ++
      encode_bytes 1 (sensitivity_gamma_sign record) ++
      encode_bytes 7 (sensitivity_gamma record) ++
      encode_bytes 1 (sensitivity_theta_sign record) ++
      encode_bytes 12 (sensitivity_theta record) ++
      encode_bytes 1 (sensitivity_vega_sign record) ++
      encode_bytes 12 (sensitivity_vega record) ++
      encode_bytes 1 (sensitivity_rho_sign record) ++
      encode_bytes 12 (sensitivity_rho record) ++
      encode_bytes 5 (intrinsic_volatility record) ++
      encode_bytes 10 (prerequisite_cost record) ++
      encode_bytes 6 (filler_6 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (theoretical_warrant_price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (sensitivity_delta_sign_value, bytes) =>
                      match decode_bytes 7 bytes with
                      | None => None
                      | Some (sensitivity_delta_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (sensitivity_gamma_sign_value, bytes) =>
                              match decode_bytes 7 bytes with
                              | None => None
                              | Some (sensitivity_gamma_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sensitivity_theta_sign_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (sensitivity_theta_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (sensitivity_vega_sign_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (sensitivity_vega_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (sensitivity_rho_sign_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (sensitivity_rho_value, bytes) =>
                                                          match decode_bytes 5 bytes with
                                                          | None => None
                                                          | Some (intrinsic_volatility_value, bytes) =>
                                                              match decode_bytes 10 bytes with
                                                              | None => None
                                                              | Some (prerequisite_cost_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (filler_6_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (end_keyword_value, bytes) =>
                                                                          Some ({| isin := isin_value; time := time_value; theoretical_warrant_price := theoretical_warrant_price_value; sensitivity_delta_sign := sensitivity_delta_sign_value; sensitivity_delta := sensitivity_delta_value; sensitivity_gamma_sign := sensitivity_gamma_sign_value; sensitivity_gamma := sensitivity_gamma_value; sensitivity_theta_sign := sensitivity_theta_sign_value; sensitivity_theta := sensitivity_theta_value; sensitivity_vega_sign := sensitivity_vega_sign_value; sensitivity_vega := sensitivity_vega_value; sensitivity_rho_sign := sensitivity_rho_sign_value; sensitivity_rho := sensitivity_rho_value; intrinsic_volatility := intrinsic_volatility_value; prerequisite_cost := prerequisite_cost_value; filler_6 := filler_6_value; end_keyword := end_keyword_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 105.
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

  End ElwInvestmentIndicatorSensitivityMessage.

  Module EtnIivMessage.

    (** ETN intraday indicative value. Previous-day and during-market/final iIV per ETN. *)
    Record t := {
      isin : list byte;
      hours : list byte;
      previous_days_iv : list byte;
      during_market_hours_final_iv : list byte;
      filler_28 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (hours record) = 6 /\
      Datatypes.length (previous_days_iv record) = 9 /\
      Datatypes.length (during_market_hours_final_iv record) = 9 /\
      Datatypes.length (filler_28 record) = 28 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (hours record) ++
      encode_bytes 9 (previous_days_iv record) ++
      encode_bytes 9 (during_market_hours_final_iv record) ++
      encode_bytes 28 (filler_28 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (hours_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (previous_days_iv_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (during_market_hours_final_iv_value, bytes) =>
                      match decode_bytes 28 bytes with
                      | None => None
                      | Some (filler_28_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| isin := isin_value; hours := hours_value; previous_days_iv := previous_days_iv_value; during_market_hours_final_iv := during_market_hours_final_iv_value; filler_28 := filler_28_value; end_keyword := end_keyword_value |}, bytes)
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

  End EtnIivMessage.

  Module EtnDisparateRatioMessage.

    (** ETN signed disparate ratio per ETN. *)
    Record t := {
      isin : list byte;
      seq_number : list byte;
      date : list byte;
      disparate_ratio_sign : list byte;
      disparate_ratio : list byte;
      filler_56 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (seq_number record) = 8 /\
      Datatypes.length (date record) = 8 /\
      Datatypes.length (disparate_ratio_sign record) = 1 /\
      Datatypes.length (disparate_ratio record) = 9 /\
      Datatypes.length (filler_56 record) = 56 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin record) ++
      encode_bytes 8 (seq_number record) ++
      encode_bytes 8 (date record) ++
      encode_bytes 1 (disparate_ratio_sign record) ++
      encode_bytes 9 (disparate_ratio record) ++
      encode_bytes 56 (filler_56 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (seq_number_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (date_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (disparate_ratio_sign_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (disparate_ratio_value, bytes) =>
                          match decode_bytes 56 bytes with
                          | None => None
                          | Some (filler_56_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| isin := isin_value; seq_number := seq_number_value; date := date_value; disparate_ratio_sign := disparate_ratio_sign_value; disparate_ratio := disparate_ratio_value; filler_56 := filler_56_value; end_keyword := end_keyword_value |}, bytes)
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

  End EtnDisparateRatioMessage.

  Module LoanTransactionAvailableQuantityMessage.

    (** Loan transaction available quantity public disclosure. Reports the available stock lending quantity for one issue (ISIN) in shares. *)
    Record t := {
      issue_code : list byte;
      business_code : list byte;
      available_lending_quantity : list byte;
      filler_19 : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_code record) = 12 /\
      Datatypes.length (business_code record) = 3 /\
      Datatypes.length (available_lending_quantity record) = 10 /\
      Datatypes.length (filler_19 record) = 19 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (issue_code record) ++
      encode_bytes 3 (business_code record) ++
      encode_bytes 10 (available_lending_quantity record) ++
      encode_bytes 19 (filler_19 record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (issue_code_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (business_code_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (available_lending_quantity_value, bytes) =>
                  match decode_bytes 19 bytes with
                  | None => None
                  | Some (filler_19_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| issue_code := issue_code_value; business_code := business_code_value; available_lending_quantity := available_lending_quantity_value; filler_19 := filler_19_value; end_keyword := end_keyword_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
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

  End LoanTransactionAvailableQuantityMessage.

End KoscomMdcsRealtimeKoscomV120.
