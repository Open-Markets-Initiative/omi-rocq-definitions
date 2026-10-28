From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group IndexStatistics

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
      - a run filling what frames it
      - a run counted by a field
  *)

Module TseEquitiesIndexStatisticsV195.

  Module MessageSerialNo.

    (** Numbered from 1 on each Multicast Group, with the multicast group number in the first to third byte *)
    Record t := {
      multicast_group_number : list byte;
      sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (multicast_group_number record) = 3 /\
      Datatypes.length (sequence_number record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (multicast_group_number record) ++
      encode_bytes 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (multicast_group_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              Some ({| multicast_group_number := multicast_group_number_value; sequence_number := sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageSerialNo.

  Module IssueClassification.

    (** Set in issue realtime message and issue basic message. In the case of Control, Index and Statistics Message, space is set. *)
    Record t := {
      issue_classification_large_classification : list byte;
      issue_classification_medium_classification : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (issue_classification_large_classification record) = 2 /\
      Datatypes.length (issue_classification_medium_classification record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (issue_classification_large_classification record) ++
      encode_bytes 2 (issue_classification_medium_classification record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (issue_classification_large_classification_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (issue_classification_medium_classification_value, bytes) =>
              Some ({| issue_classification_large_classification := issue_classification_large_classification_value; issue_classification_medium_classification := issue_classification_medium_classification_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IssueClassification.

  Module StockIssueCode.

    (** Issue Code layout a. Stocks, used when Issue Classification Large Classification is 01 Stock-Related. FLEX Issue Code is set with right-align. *)
    Record t := {
      stock_space : list byte;
      stock_proper_name_code : list byte;
      stock_reserved_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock_space record) = 7 /\
      Datatypes.length (stock_proper_name_code record) = 4 /\
      Datatypes.length (stock_reserved_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (stock_space record) ++
      encode_bytes 4 (stock_proper_name_code record) ++
      encode_bytes 1 (stock_reserved_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (stock_space_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (stock_proper_name_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (stock_reserved_code_value, bytes) =>
                  Some ({| stock_space := stock_space_value; stock_proper_name_code := stock_proper_name_code_value; stock_reserved_code := stock_reserved_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockIssueCode.

  Module CBIssueCode.

    (** Issue Code layout used when Issue Classification Large Classification is 02 CB-Related. The figure carries no label of its own in 5.3.3 (7). FLEX Issue Code is set with right-align. *)
    Record t := {
      c_b_space : list byte;
      c_b_reserved_code : list byte;
      time_symbol : list byte;
      c_b_proper_name_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (c_b_space record) = 3 /\
      Datatypes.length (c_b_reserved_code record) = 1 /\
      Datatypes.length (time_symbol record) = 4 /\
      Datatypes.length (c_b_proper_name_code record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (c_b_space record) ++
      encode_bytes 1 (c_b_reserved_code record) ++
      encode_bytes 4 (time_symbol record) ++
      encode_bytes 4 (c_b_proper_name_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (c_b_space_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (c_b_reserved_code_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (time_symbol_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (c_b_proper_name_code_value, bytes) =>
                      Some ({| c_b_space := c_b_space_value; c_b_reserved_code := c_b_reserved_code_value; time_symbol := time_symbol_value; c_b_proper_name_code := c_b_proper_name_code_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CBIssueCode.

  Module TotalMarketValue.

    (** Total market value *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      total_market_value_c_14 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (total_market_value_c_14 record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (total_market_value_c_14 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (total_market_value_c_14_value, bytes) =>
              Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; total_market_value_c_14 := total_market_value_c_14_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TotalMarketValue.

  Module MarketValueDayOnDayComparison.

    (** Market value Day-on-day comparison *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      day_on_day_comparison_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (day_on_day_comparison_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (day_on_day_comparison_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; day_on_day_comparison_c_14 := day_on_day_comparison_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketValueDayOnDayComparison.

  Module MarketValueMessage.

    (** In this tag, total market value information for each market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      time_c_6_hhmm : list byte;
      issue_classification_code : list byte;
      total_market_value : TotalMarketValue.t;
      market_value_day_on_day_comparison : MarketValueDayOnDayComparison.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (time_c_6_hhmm record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      TotalMarketValue.bounded (total_market_value record) /\
      MarketValueDayOnDayComparison.bounded (market_value_day_on_day_comparison record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (time_c_6_hhmm record) ++
      encode_bytes 4 (issue_classification_code record) ++
      TotalMarketValue.encode (total_market_value record) ++
      MarketValueDayOnDayComparison.encode (market_value_day_on_day_comparison record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_c_6_hhmm_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match TotalMarketValue.decode bytes with
                  | None => None
                  | Some (total_market_value_value, bytes) =>
                      match MarketValueDayOnDayComparison.decode bytes with
                      | None => None
                      | Some (market_value_day_on_day_comparison_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; time_c_6_hhmm := time_c_6_hhmm_value; issue_classification_code := issue_classification_code_value; total_market_value := total_market_value_value; market_value_day_on_day_comparison := market_value_day_on_day_comparison_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !TotalMarketValue.encode_length, !MarketValueDayOnDayComparison.encode_length. reflexivity.
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
      rewrite TotalMarketValue.decode_encode by exact bound_3.
      rewrite MarketValueDayOnDayComparison.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TotalMarketValue.eq_dec | apply MarketValueDayOnDayComparison.eq_dec]. Defined.

  End MarketValueMessage.

  Module SimpleYield.

    (** Simple yield *)
    Record t := {
      simple_yield_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (simple_yield_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (simple_yield_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (simple_yield_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| simple_yield_c_8 := simple_yield_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleYield.

  Module YieldDayOnDayComparison.

    (** Yield Day-on-day comparison *)
    Record t := {
      day_on_day_comparison_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (day_on_day_comparison_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (day_on_day_comparison_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (day_on_day_comparison_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| day_on_day_comparison_c_8 := day_on_day_comparison_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End YieldDayOnDayComparison.

  Module SimpleYieldMessage.

    (** In this tag, simple yield information for each market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      time_c_6_hhmm : list byte;
      issue_classification_code : list byte;
      simple_yield : SimpleYield.t;
      yield_day_on_day_comparison : YieldDayOnDayComparison.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (time_c_6_hhmm record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      SimpleYield.bounded (simple_yield record) /\
      YieldDayOnDayComparison.bounded (yield_day_on_day_comparison record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (time_c_6_hhmm record) ++
      encode_bytes 4 (issue_classification_code record) ++
      SimpleYield.encode (simple_yield record) ++
      YieldDayOnDayComparison.encode (yield_day_on_day_comparison record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_c_6_hhmm_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match SimpleYield.decode bytes with
                  | None => None
                  | Some (simple_yield_value, bytes) =>
                      match YieldDayOnDayComparison.decode bytes with
                      | None => None
                      | Some (yield_day_on_day_comparison_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; time_c_6_hhmm := time_c_6_hhmm_value; issue_classification_code := issue_classification_code_value; simple_yield := simple_yield_value; yield_day_on_day_comparison := yield_day_on_day_comparison_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !SimpleYield.encode_length, !YieldDayOnDayComparison.encode_length. reflexivity.
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
      rewrite SimpleYield.decode_encode by exact bound_3.
      rewrite YieldDayOnDayComparison.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SimpleYield.eq_dec | apply YieldDayOnDayComparison.eq_dec]. Defined.

  End SimpleYieldMessage.

  Module WeightedYield.

    (** Weighted yield *)
    Record t := {
      weighted_yield_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (weighted_yield_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (weighted_yield_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (weighted_yield_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| weighted_yield_c_8 := weighted_yield_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End WeightedYield.

  Module YieldDayOnDayComparison2.

    (** Yield Day-on-day comparison *)
    Record t := {
      day_on_day_comparison_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (day_on_day_comparison_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (day_on_day_comparison_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (day_on_day_comparison_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| day_on_day_comparison_c_8 := day_on_day_comparison_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End YieldDayOnDayComparison2.

  Module WeightedYieldMessage.

    (** In this tag, weighted yield information for each market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      time_c_6_hhmm : list byte;
      issue_classification_code : list byte;
      weighted_yield : WeightedYield.t;
      yield_day_on_day_comparison : YieldDayOnDayComparison2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (time_c_6_hhmm record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      WeightedYield.bounded (weighted_yield record) /\
      YieldDayOnDayComparison2.bounded (yield_day_on_day_comparison record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (time_c_6_hhmm record) ++
      encode_bytes 4 (issue_classification_code record) ++
      WeightedYield.encode (weighted_yield record) ++
      YieldDayOnDayComparison2.encode (yield_day_on_day_comparison record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_c_6_hhmm_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match WeightedYield.decode bytes with
                  | None => None
                  | Some (weighted_yield_value, bytes) =>
                      match YieldDayOnDayComparison2.decode bytes with
                      | None => None
                      | Some (yield_day_on_day_comparison_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; time_c_6_hhmm := time_c_6_hhmm_value; issue_classification_code := issue_classification_code_value; weighted_yield := weighted_yield_value; yield_day_on_day_comparison := yield_day_on_day_comparison_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !WeightedYield.encode_length, !YieldDayOnDayComparison2.encode_length. reflexivity.
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
      rewrite WeightedYield.decode_encode by exact bound_3.
      rewrite YieldDayOnDayComparison2.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply WeightedYield.eq_dec | apply YieldDayOnDayComparison2.eq_dec]. Defined.

  End WeightedYieldMessage.

  Module SimpleStockPriceAverage.

    (** Simple stock price average *)
    Record t := {
      unit_flag : list byte;
      simple_stock_price_average_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (simple_stock_price_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (simple_stock_price_average_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (simple_stock_price_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; simple_stock_price_average_c_14 := simple_stock_price_average_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleStockPriceAverage.

  Module StockPriceAverageDayOnDayComparison.

    (** Stock price average Day-on-day comparison *)
    Record t := {
      unit_flag : list byte;
      day_on_day_comparison_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (day_on_day_comparison_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (day_on_day_comparison_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; day_on_day_comparison_c_14 := day_on_day_comparison_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockPriceAverageDayOnDayComparison.

  Module SimpleStockPriceAverageMessage.

    (** In this tag, simple stock price average information for each market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      issue_classification_code : list byte;
      simple_stock_price_average : SimpleStockPriceAverage.t;
      stock_price_average_day_on_day_comparison : StockPriceAverageDayOnDayComparison.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      SimpleStockPriceAverage.bounded (simple_stock_price_average record) /\
      StockPriceAverageDayOnDayComparison.bounded (stock_price_average_day_on_day_comparison record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      encode_bytes 4 (issue_classification_code record) ++
      SimpleStockPriceAverage.encode (simple_stock_price_average record) ++
      StockPriceAverageDayOnDayComparison.encode (stock_price_average_day_on_day_comparison record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match SimpleStockPriceAverage.decode bytes with
                  | None => None
                  | Some (simple_stock_price_average_value, bytes) =>
                      match StockPriceAverageDayOnDayComparison.decode bytes with
                      | None => None
                      | Some (stock_price_average_day_on_day_comparison_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; issue_classification_code := issue_classification_code_value; simple_stock_price_average := simple_stock_price_average_value; stock_price_average_day_on_day_comparison := stock_price_average_day_on_day_comparison_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !SimpleStockPriceAverage.encode_length, !StockPriceAverageDayOnDayComparison.encode_length. reflexivity.
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
      rewrite SimpleStockPriceAverage.decode_encode by exact bound_3.
      rewrite StockPriceAverageDayOnDayComparison.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SimpleStockPriceAverage.eq_dec | apply StockPriceAverageDayOnDayComparison.eq_dec]. Defined.

  End SimpleStockPriceAverageMessage.

  Module WeightedStockPriceAverage.

    (** Weighted stock price average *)
    Record t := {
      unit_flag : list byte;
      weighted_stock_price_average_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (weighted_stock_price_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (weighted_stock_price_average_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (weighted_stock_price_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; weighted_stock_price_average_c_14 := weighted_stock_price_average_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End WeightedStockPriceAverage.

  Module StockPriceAverageDayOnDayComparison2.

    (** Stock price average Day-on-day comparison *)
    Record t := {
      unit_flag : list byte;
      day_on_day_comparison_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (day_on_day_comparison_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (day_on_day_comparison_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; day_on_day_comparison_c_14 := day_on_day_comparison_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockPriceAverageDayOnDayComparison2.

  Module WeightedStockPriceAverageMessage.

    (** In this tag, weighted stock price average information for each market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      issue_classification_code : list byte;
      weighted_stock_price_average : WeightedStockPriceAverage.t;
      stock_price_average_day_on_day_comparison : StockPriceAverageDayOnDayComparison2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      WeightedStockPriceAverage.bounded (weighted_stock_price_average record) /\
      StockPriceAverageDayOnDayComparison2.bounded (stock_price_average_day_on_day_comparison record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      encode_bytes 4 (issue_classification_code record) ++
      WeightedStockPriceAverage.encode (weighted_stock_price_average record) ++
      StockPriceAverageDayOnDayComparison2.encode (stock_price_average_day_on_day_comparison record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match WeightedStockPriceAverage.decode bytes with
                  | None => None
                  | Some (weighted_stock_price_average_value, bytes) =>
                      match StockPriceAverageDayOnDayComparison2.decode bytes with
                      | None => None
                      | Some (stock_price_average_day_on_day_comparison_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; issue_classification_code := issue_classification_code_value; weighted_stock_price_average := weighted_stock_price_average_value; stock_price_average_day_on_day_comparison := stock_price_average_day_on_day_comparison_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !WeightedStockPriceAverage.encode_length, !StockPriceAverageDayOnDayComparison2.encode_length. reflexivity.
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
      rewrite WeightedStockPriceAverage.decode_encode by exact bound_3.
      rewrite StockPriceAverageDayOnDayComparison2.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply WeightedStockPriceAverage.eq_dec | apply StockPriceAverageDayOnDayComparison2.eq_dec]. Defined.

  End WeightedStockPriceAverageMessage.

  Module SimpleStockPriceAverage2.

    (** Simple stock price average *)
    Record t := {
      unit_flag : list byte;
      simple_stock_price_average_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (simple_stock_price_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (simple_stock_price_average_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (simple_stock_price_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; simple_stock_price_average_c_14 := simple_stock_price_average_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleStockPriceAverage2.

  Module StockPriceAverageDayOnDayComparison3.

    (** Stock price average Day-on-day comparison *)
    Record t := {
      unit_flag : list byte;
      day_on_day_comparison_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (day_on_day_comparison_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (day_on_day_comparison_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; day_on_day_comparison_c_14 := day_on_day_comparison_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockPriceAverageDayOnDayComparison3.

  Module SimpleStockPriceAverageByIndustryMessage.

    (** In this tag, simple stock price average information by industry classification will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      industry_code : list byte;
      simple_stock_price_average : SimpleStockPriceAverage2.t;
      stock_price_average_day_on_day_comparison : StockPriceAverageDayOnDayComparison3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Datatypes.length (industry_code record) = 4 /\
      SimpleStockPriceAverage2.bounded (simple_stock_price_average record) /\
      StockPriceAverageDayOnDayComparison3.bounded (stock_price_average_day_on_day_comparison record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      encode_bytes 4 (industry_code record) ++
      SimpleStockPriceAverage2.encode (simple_stock_price_average record) ++
      StockPriceAverageDayOnDayComparison3.encode (stock_price_average_day_on_day_comparison record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (industry_code_value, bytes) =>
                  match SimpleStockPriceAverage2.decode bytes with
                  | None => None
                  | Some (simple_stock_price_average_value, bytes) =>
                      match StockPriceAverageDayOnDayComparison3.decode bytes with
                      | None => None
                      | Some (stock_price_average_day_on_day_comparison_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; industry_code := industry_code_value; simple_stock_price_average := simple_stock_price_average_value; stock_price_average_day_on_day_comparison := stock_price_average_day_on_day_comparison_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !SimpleStockPriceAverage2.encode_length, !StockPriceAverageDayOnDayComparison3.encode_length. reflexivity.
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
      rewrite SimpleStockPriceAverage2.decode_encode by exact bound_3.
      rewrite StockPriceAverageDayOnDayComparison3.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply SimpleStockPriceAverage2.eq_dec | apply StockPriceAverageDayOnDayComparison3.eq_dec]. Defined.

  End SimpleStockPriceAverageByIndustryMessage.

  Module OverallSimpleAverage.

    (** Overall Simple average *)
    Record t := {
      unit_flag : list byte;
      simple_average_c_14 : list byte;
      sign : list byte;
      second_unit_flag : list byte;
      day_on_day_comparison_c_14 : list byte;
      second_sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (simple_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (second_unit_flag record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_14 record) = 14 /\
      Datatypes.length (second_sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (simple_average_c_14 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 1 (second_unit_flag record) ++
      encode_bytes 14 (day_on_day_comparison_c_14 record) ++
      encode_bytes 1 (second_sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (simple_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (second_unit_flag_value, bytes) =>
                      match decode_bytes 14 bytes with
                      | None => None
                      | Some (day_on_day_comparison_c_14_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_sign_value, bytes) =>
                              Some ({| unit_flag := unit_flag_value; simple_average_c_14 := simple_average_c_14_value; sign := sign_value; second_unit_flag := second_unit_flag_value; day_on_day_comparison_c_14 := day_on_day_comparison_c_14_value; second_sign := second_sign_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End OverallSimpleAverage.

  Module OverallDivergenceAverage.

    (** Overall Divergence average *)
    Record t := {
      divergence_average_c_8 : list byte;
      sign : list byte;
      day_on_day_comparison_c_8 : list byte;
      second_sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (divergence_average_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_8 record) = 8 /\
      Datatypes.length (second_sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (divergence_average_c_8 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 8 (day_on_day_comparison_c_8 record) ++
      encode_bytes 1 (second_sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (divergence_average_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (day_on_day_comparison_c_8_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (second_sign_value, bytes) =>
                      Some ({| divergence_average_c_8 := divergence_average_c_8_value; sign := sign_value; day_on_day_comparison_c_8 := day_on_day_comparison_c_8_value; second_sign := second_sign_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OverallDivergenceAverage.

  Module OverallParityAverage.

    (** Overall Parity average *)
    Record t := {
      unit_flag : list byte;
      parity_average_c_14 : list byte;
      sign : list byte;
      second_unit_flag : list byte;
      day_on_day_comparison_c_14 : list byte;
      second_sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (parity_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (second_unit_flag record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_14 record) = 14 /\
      Datatypes.length (second_sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (parity_average_c_14 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 1 (second_unit_flag record) ++
      encode_bytes 14 (day_on_day_comparison_c_14 record) ++
      encode_bytes 1 (second_sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (parity_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (second_unit_flag_value, bytes) =>
                      match decode_bytes 14 bytes with
                      | None => None
                      | Some (day_on_day_comparison_c_14_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (second_sign_value, bytes) =>
                              Some ({| unit_flag := unit_flag_value; parity_average_c_14 := parity_average_c_14_value; sign := sign_value; second_unit_flag := second_unit_flag_value; day_on_day_comparison_c_14 := day_on_day_comparison_c_14_value; second_sign := second_sign_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End OverallParityAverage.

  Module OverallDirectYieldAverage.

    (** Overall Direct yield average *)
    Record t := {
      direct_yield_average_c_8 : list byte;
      sign : list byte;
      day_on_day_comparison_c_8 : list byte;
      second_sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (direct_yield_average_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_8 record) = 8 /\
      Datatypes.length (second_sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (direct_yield_average_c_8 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 8 (day_on_day_comparison_c_8 record) ++
      encode_bytes 1 (second_sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (direct_yield_average_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (day_on_day_comparison_c_8_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (second_sign_value, bytes) =>
                      Some ({| direct_yield_average_c_8 := direct_yield_average_c_8_value; sign := sign_value; day_on_day_comparison_c_8 := day_on_day_comparison_c_8_value; second_sign := second_sign_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OverallDirectYieldAverage.

  Module Overall.

    (** Overall *)
    Record t := {
      overall_simple_average : OverallSimpleAverage.t;
      overall_divergence_average : OverallDivergenceAverage.t;
      overall_parity_average : OverallParityAverage.t;
      overall_direct_yield_average : OverallDirectYieldAverage.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      OverallSimpleAverage.bounded (overall_simple_average record) /\
      OverallDivergenceAverage.bounded (overall_divergence_average record) /\
      OverallParityAverage.bounded (overall_parity_average record) /\
      OverallDirectYieldAverage.bounded (overall_direct_yield_average record).

    Definition encode (record : t) : list byte :=
      OverallSimpleAverage.encode (overall_simple_average record) ++
      OverallDivergenceAverage.encode (overall_divergence_average record) ++
      OverallParityAverage.encode (overall_parity_average record) ++
      OverallDirectYieldAverage.encode (overall_direct_yield_average record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match OverallSimpleAverage.decode bytes with
      | None => None
      | Some (overall_simple_average_value, bytes) =>
          match OverallDivergenceAverage.decode bytes with
          | None => None
          | Some (overall_divergence_average_value, bytes) =>
              match OverallParityAverage.decode bytes with
              | None => None
              | Some (overall_parity_average_value, bytes) =>
                  match OverallDirectYieldAverage.decode bytes with
                  | None => None
                  | Some (overall_direct_yield_average_value, bytes) =>
                      Some ({| overall_simple_average := overall_simple_average_value; overall_divergence_average := overall_divergence_average_value; overall_parity_average := overall_parity_average_value; overall_direct_yield_average := overall_direct_yield_average_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 100.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !OverallSimpleAverage.encode_length, !OverallDivergenceAverage.encode_length, !OverallParityAverage.encode_length, !OverallDirectYieldAverage.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite OverallSimpleAverage.decode_encode by exact bound_0.
      rewrite OverallDivergenceAverage.decode_encode by exact bound_1.
      rewrite OverallParityAverage.decode_encode by exact bound_2.
      rewrite OverallDirectYieldAverage.decode_encode by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply OverallSimpleAverage.eq_dec | apply OverallDivergenceAverage.eq_dec | apply OverallParityAverage.eq_dec | apply OverallDirectYieldAverage.eq_dec]. Defined.

  End Overall.

  Module SimpleAverage.

    (** Simple average *)
    Record t := {
      unit_flag : list byte;
      simple_average_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (simple_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (simple_average_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (simple_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; simple_average_c_14 := simple_average_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleAverage.

  Module DivergenceAverage.

    (** Divergence average *)
    Record t := {
      divergence_average_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (divergence_average_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (divergence_average_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (divergence_average_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| divergence_average_c_8 := divergence_average_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DivergenceAverage.

  Module ParityAverage.

    (** Parity average *)
    Record t := {
      unit_flag : list byte;
      parity_average_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (parity_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (parity_average_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (parity_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; parity_average_c_14 := parity_average_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParityAverage.

  Module DirectYieldAverage.

    (** Direct yield average *)
    Record t := {
      direct_yield_average_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (direct_yield_average_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (direct_yield_average_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (direct_yield_average_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| direct_yield_average_c_8 := direct_yield_average_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DirectYieldAverage.

  Module Parity100OrHigher.

    (** Parity 100 or higher *)
    Record t := {
      simple_average : SimpleAverage.t;
      divergence_average : DivergenceAverage.t;
      parity_average : ParityAverage.t;
      direct_yield_average : DirectYieldAverage.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SimpleAverage.bounded (simple_average record) /\
      DivergenceAverage.bounded (divergence_average record) /\
      ParityAverage.bounded (parity_average record) /\
      DirectYieldAverage.bounded (direct_yield_average record).

    Definition encode (record : t) : list byte :=
      SimpleAverage.encode (simple_average record) ++
      DivergenceAverage.encode (divergence_average record) ++
      ParityAverage.encode (parity_average record) ++
      DirectYieldAverage.encode (direct_yield_average record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SimpleAverage.decode bytes with
      | None => None
      | Some (simple_average_value, bytes) =>
          match DivergenceAverage.decode bytes with
          | None => None
          | Some (divergence_average_value, bytes) =>
              match ParityAverage.decode bytes with
              | None => None
              | Some (parity_average_value, bytes) =>
                  match DirectYieldAverage.decode bytes with
                  | None => None
                  | Some (direct_yield_average_value, bytes) =>
                      Some ({| simple_average := simple_average_value; divergence_average := divergence_average_value; parity_average := parity_average_value; direct_yield_average := direct_yield_average_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SimpleAverage.encode_length, !DivergenceAverage.encode_length, !ParityAverage.encode_length, !DirectYieldAverage.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SimpleAverage.decode_encode by exact bound_0.
      rewrite DivergenceAverage.decode_encode by exact bound_1.
      rewrite ParityAverage.decode_encode by exact bound_2.
      rewrite DirectYieldAverage.decode_encode by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply SimpleAverage.eq_dec | apply DivergenceAverage.eq_dec | apply ParityAverage.eq_dec | apply DirectYieldAverage.eq_dec]. Defined.

  End Parity100OrHigher.

  Module SimpleAverage2.

    (** Simple average *)
    Record t := {
      unit_flag : list byte;
      simple_average_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (simple_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (simple_average_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (simple_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; simple_average_c_14 := simple_average_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleAverage2.

  Module DivergenceAverage2.

    (** Divergence average *)
    Record t := {
      divergence_average_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (divergence_average_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (divergence_average_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (divergence_average_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| divergence_average_c_8 := divergence_average_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DivergenceAverage2.

  Module ParityAverage2.

    (** Parity average *)
    Record t := {
      unit_flag : list byte;
      parity_average_c_14 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (parity_average_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (parity_average_c_14 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (parity_average_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  Some ({| unit_flag := unit_flag_value; parity_average_c_14 := parity_average_c_14_value; sign := sign_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ParityAverage2.

  Module DirectYieldAverage2.

    (** Direct yield average *)
    Record t := {
      direct_yield_average_c_8 : list byte;
      sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (direct_yield_average_c_8 record) = 8 /\
      Datatypes.length (sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (direct_yield_average_c_8 record) ++
      encode_bytes 1 (sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (direct_yield_average_c_8_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              Some ({| direct_yield_average_c_8 := direct_yield_average_c_8_value; sign := sign_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DirectYieldAverage2.

  Module ParityLessThan100.

    (** Parity less than 100 *)
    Record t := {
      simple_average : SimpleAverage2.t;
      divergence_average : DivergenceAverage2.t;
      parity_average : ParityAverage2.t;
      direct_yield_average : DirectYieldAverage2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      SimpleAverage2.bounded (simple_average record) /\
      DivergenceAverage2.bounded (divergence_average record) /\
      ParityAverage2.bounded (parity_average record) /\
      DirectYieldAverage2.bounded (direct_yield_average record).

    Definition encode (record : t) : list byte :=
      SimpleAverage2.encode (simple_average record) ++
      DivergenceAverage2.encode (divergence_average record) ++
      ParityAverage2.encode (parity_average record) ++
      DirectYieldAverage2.encode (direct_yield_average record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match SimpleAverage2.decode bytes with
      | None => None
      | Some (simple_average_value, bytes) =>
          match DivergenceAverage2.decode bytes with
          | None => None
          | Some (divergence_average_value, bytes) =>
              match ParityAverage2.decode bytes with
              | None => None
              | Some (parity_average_value, bytes) =>
                  match DirectYieldAverage2.decode bytes with
                  | None => None
                  | Some (direct_yield_average_value, bytes) =>
                      Some ({| simple_average := simple_average_value; divergence_average := divergence_average_value; parity_average := parity_average_value; direct_yield_average := direct_yield_average_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !SimpleAverage2.encode_length, !DivergenceAverage2.encode_length, !ParityAverage2.encode_length, !DirectYieldAverage2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite SimpleAverage2.decode_encode by exact bound_0.
      rewrite DivergenceAverage2.decode_encode by exact bound_1.
      rewrite ParityAverage2.decode_encode by exact bound_2.
      rewrite DirectYieldAverage2.decode_encode by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply SimpleAverage2.eq_dec | apply DivergenceAverage2.eq_dec | apply ParityAverage2.eq_dec | apply DirectYieldAverage2.eq_dec]. Defined.

  End ParityLessThan100.

  Module JapaneseYenCbIndicatorMessage.

    (** In this tag, CB indicator (overall, parity 100 or higher, and parity less than 100) information will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      overall : Overall.t;
      parity_100_or_higher : Parity100OrHigher.t;
      parity_less_than_100 : ParityLessThan100.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Overall.bounded (overall record) /\
      Parity100OrHigher.bounded (parity_100_or_higher record) /\
      ParityLessThan100.bounded (parity_less_than_100 record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      Overall.encode (overall record) ++
      Parity100OrHigher.encode (parity_100_or_higher record) ++
      ParityLessThan100.encode (parity_less_than_100 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match Overall.decode bytes with
              | None => None
              | Some (overall_value, bytes) =>
                  match Parity100OrHigher.decode bytes with
                  | None => None
                  | Some (parity_100_or_higher_value, bytes) =>
                      match ParityLessThan100.decode bytes with
                      | None => None
                      | Some (parity_less_than_100_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; overall := overall_value; parity_100_or_higher := parity_100_or_higher_value; parity_less_than_100 := parity_less_than_100_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 208.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Overall.encode_length, !Parity100OrHigher.encode_length, !ParityLessThan100.encode_length. reflexivity.
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
      rewrite Overall.decode_encode by exact bound_2.
      rewrite Parity100OrHigher.decode_encode by exact bound_3.
      rewrite ParityLessThan100.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Overall.eq_dec | apply Parity100OrHigher.eq_dec | apply ParityLessThan100.eq_dec]. Defined.

  End JapaneseYenCbIndicatorMessage.

  Module NumberOfActiveIssues.

    (** Number of active issues *)
    Record t := {
      number_of_issues : list byte;
      ratio : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (number_of_issues record) = 5 /\
      Datatypes.length (ratio record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (number_of_issues record) ++
      encode_bytes 5 (ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (number_of_issues_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (ratio_value, bytes) =>
              Some ({| number_of_issues := number_of_issues_value; ratio := ratio_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NumberOfActiveIssues.

  Module NumberOfGainers.

    (** Number of gainers *)
    Record t := {
      number_of_issues : list byte;
      ratio : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (number_of_issues record) = 5 /\
      Datatypes.length (ratio record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (number_of_issues record) ++
      encode_bytes 5 (ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (number_of_issues_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (ratio_value, bytes) =>
              Some ({| number_of_issues := number_of_issues_value; ratio := ratio_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NumberOfGainers.

  Module NumberOfDecliners.

    (** Number of decliners *)
    Record t := {
      number_of_issues : list byte;
      ratio : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (number_of_issues record) = 5 /\
      Datatypes.length (ratio record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (number_of_issues record) ++
      encode_bytes 5 (ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (number_of_issues_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (ratio_value, bytes) =>
              Some ({| number_of_issues := number_of_issues_value; ratio := ratio_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NumberOfDecliners.

  Module NumberOfIssuesWithNoChange.

    (** Number of issues with no change *)
    Record t := {
      number_of_issues : list byte;
      ratio : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (number_of_issues record) = 5 /\
      Datatypes.length (ratio record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (number_of_issues record) ++
      encode_bytes 5 (ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (number_of_issues_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (ratio_value, bytes) =>
              Some ({| number_of_issues := number_of_issues_value; ratio := ratio_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NumberOfIssuesWithNoChange.

  Module NumberOfIssuesWithNoComparison.

    (** Number of issues with no comparison *)
    Record t := {
      number_of_issues : list byte;
      ratio : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (number_of_issues record) = 5 /\
      Datatypes.length (ratio record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (number_of_issues record) ++
      encode_bytes 5 (ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (number_of_issues_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (ratio_value, bytes) =>
              Some ({| number_of_issues := number_of_issues_value; ratio := ratio_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NumberOfIssuesWithNoComparison.

  Module NumberOfInactiveIssues.

    (** Number of inactive issues *)
    Record t := {
      number_of_issues : list byte;
      ratio : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (number_of_issues record) = 5 /\
      Datatypes.length (ratio record) = 5.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (number_of_issues record) ++
      encode_bytes 5 (ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (number_of_issues_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (ratio_value, bytes) =>
              Some ({| number_of_issues := number_of_issues_value; ratio := ratio_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NumberOfInactiveIssues.

  Module NumberOfGainersDeclinersMessage.

    (** In this tag, number of listed issues and number of gainers/decliners information by market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      issue_classification_code : list byte;
      number_of_listed_companies : list byte;
      number_of_listed_issues : list byte;
      number_of_active_issues : NumberOfActiveIssues.t;
      number_of_gainers : NumberOfGainers.t;
      number_of_decliners : NumberOfDecliners.t;
      number_of_issues_with_no_change : NumberOfIssuesWithNoChange.t;
      number_of_issues_with_no_comparison : NumberOfIssuesWithNoComparison.t;
      number_of_inactive_issues : NumberOfInactiveIssues.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      Datatypes.length (number_of_listed_companies record) = 5 /\
      Datatypes.length (number_of_listed_issues record) = 5 /\
      NumberOfActiveIssues.bounded (number_of_active_issues record) /\
      NumberOfGainers.bounded (number_of_gainers record) /\
      NumberOfDecliners.bounded (number_of_decliners record) /\
      NumberOfIssuesWithNoChange.bounded (number_of_issues_with_no_change record) /\
      NumberOfIssuesWithNoComparison.bounded (number_of_issues_with_no_comparison record) /\
      NumberOfInactiveIssues.bounded (number_of_inactive_issues record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      encode_bytes 4 (issue_classification_code record) ++
      encode_bytes 5 (number_of_listed_companies record) ++
      encode_bytes 5 (number_of_listed_issues record) ++
      NumberOfActiveIssues.encode (number_of_active_issues record) ++
      NumberOfGainers.encode (number_of_gainers record) ++
      NumberOfDecliners.encode (number_of_decliners record) ++
      NumberOfIssuesWithNoChange.encode (number_of_issues_with_no_change record) ++
      NumberOfIssuesWithNoComparison.encode (number_of_issues_with_no_comparison record) ++
      NumberOfInactiveIssues.encode (number_of_inactive_issues record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match decode_bytes 5 bytes with
                  | None => None
                  | Some (number_of_listed_companies_value, bytes) =>
                      match decode_bytes 5 bytes with
                      | None => None
                      | Some (number_of_listed_issues_value, bytes) =>
                          match NumberOfActiveIssues.decode bytes with
                          | None => None
                          | Some (number_of_active_issues_value, bytes) =>
                              match NumberOfGainers.decode bytes with
                              | None => None
                              | Some (number_of_gainers_value, bytes) =>
                                  match NumberOfDecliners.decode bytes with
                                  | None => None
                                  | Some (number_of_decliners_value, bytes) =>
                                      match NumberOfIssuesWithNoChange.decode bytes with
                                      | None => None
                                      | Some (number_of_issues_with_no_change_value, bytes) =>
                                          match NumberOfIssuesWithNoComparison.decode bytes with
                                          | None => None
                                          | Some (number_of_issues_with_no_comparison_value, bytes) =>
                                              match NumberOfInactiveIssues.decode bytes with
                                              | None => None
                                              | Some (number_of_inactive_issues_value, bytes) =>
                                                  Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; issue_classification_code := issue_classification_code_value; number_of_listed_companies := number_of_listed_companies_value; number_of_listed_issues := number_of_listed_issues_value; number_of_active_issues := number_of_active_issues_value; number_of_gainers := number_of_gainers_value; number_of_decliners := number_of_decliners_value; number_of_issues_with_no_change := number_of_issues_with_no_change_value; number_of_issues_with_no_comparison := number_of_issues_with_no_comparison_value; number_of_inactive_issues := number_of_inactive_issues_value |}, bytes)
                                              end
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
      rewrite !length_app, !encode_bytes_length, !NumberOfActiveIssues.encode_length, !NumberOfGainers.encode_length, !NumberOfDecliners.encode_length, !NumberOfIssuesWithNoChange.encode_length, !NumberOfIssuesWithNoComparison.encode_length, !NumberOfInactiveIssues.encode_length. reflexivity.
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
      rewrite NumberOfActiveIssues.decode_encode by exact bound_5.
      rewrite NumberOfGainers.decode_encode by exact bound_6.
      rewrite NumberOfDecliners.decode_encode by exact bound_7.
      rewrite NumberOfIssuesWithNoChange.decode_encode by exact bound_8.
      rewrite NumberOfIssuesWithNoComparison.decode_encode by exact bound_9.
      rewrite NumberOfInactiveIssues.decode_encode by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply NumberOfActiveIssues.eq_dec | apply NumberOfGainers.eq_dec | apply NumberOfDecliners.eq_dec | apply NumberOfIssuesWithNoChange.eq_dec | apply NumberOfIssuesWithNoComparison.eq_dec | apply NumberOfInactiveIssues.eq_dec]. Defined.

  End NumberOfGainersDeclinersMessage.

  Module EstimatedTotalTradingVolume.

    (** Estimated total trading volume *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      estimated_total_trading_volume_c_14 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (estimated_total_trading_volume_c_14 record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (estimated_total_trading_volume_c_14 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (estimated_total_trading_volume_c_14_value, bytes) =>
              Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; estimated_total_trading_volume_c_14 := estimated_total_trading_volume_c_14_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EstimatedTotalTradingVolume.

  Module EstimatedTotalTradingVolumeMessage.

    (** In this tag, estimated total trading volume information for each market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      issue_classification_code : list byte;
      other_classification_code : list byte;
      estimated_total_trading_volume : EstimatedTotalTradingVolume.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      Datatypes.length (other_classification_code record) = 2 /\
      EstimatedTotalTradingVolume.bounded (estimated_total_trading_volume record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      encode_bytes 4 (issue_classification_code record) ++
      encode_bytes 2 (other_classification_code record) ++
      EstimatedTotalTradingVolume.encode (estimated_total_trading_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (other_classification_code_value, bytes) =>
                      match EstimatedTotalTradingVolume.decode bytes with
                      | None => None
                      | Some (estimated_total_trading_volume_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; issue_classification_code := issue_classification_code_value; other_classification_code := other_classification_code_value; estimated_total_trading_volume := estimated_total_trading_volume_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !EstimatedTotalTradingVolume.encode_length. reflexivity.
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
      rewrite EstimatedTotalTradingVolume.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply EstimatedTotalTradingVolume.eq_dec]. Defined.

  End EstimatedTotalTradingVolumeMessage.

  Module EstimatedTotalTurnover.

    (** Estimated total turnover *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      estimated_total_turnover_c_14 : list byte;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (estimated_total_turnover_c_14 record) = 14 /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (estimated_total_turnover_c_14 record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (estimated_total_turnover_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reserved_1_value, bytes) =>
                  Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; estimated_total_turnover_c_14 := estimated_total_turnover_c_14_value; reserved_1 := reserved_1_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EstimatedTotalTurnover.

  Module EstimatedTotalTurnoverMessage.

    (** In this tag, estimated total turnover information for each market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      issue_classification_code : list byte;
      other_classification_flag : list byte;
      estimated_total_turnover : EstimatedTotalTurnover.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      Datatypes.length (other_classification_flag record) = 2 /\
      EstimatedTotalTurnover.bounded (estimated_total_turnover record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      encode_bytes 4 (issue_classification_code record) ++
      encode_bytes 2 (other_classification_flag record) ++
      EstimatedTotalTurnover.encode (estimated_total_turnover record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (other_classification_flag_value, bytes) =>
                      match EstimatedTotalTurnover.decode bytes with
                      | None => None
                      | Some (estimated_total_turnover_value, bytes) =>
                          Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; issue_classification_code := issue_classification_code_value; other_classification_flag := other_classification_flag_value; estimated_total_turnover := estimated_total_turnover_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !EstimatedTotalTurnover.encode_length. reflexivity.
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
      rewrite EstimatedTotalTurnover.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply EstimatedTotalTurnover.eq_dec]. Defined.

  End EstimatedTotalTurnoverMessage.

  Module VwapByMarket.

    (** VWAP by market *)
    Record t := {
      unit_flag : list byte;
      vwap_by_market_c_14 : list byte;
      sign : list byte;
      reserved_1 : list byte;
      second_unit_flag : list byte;
      day_on_day_comparison_c_14 : list byte;
      second_sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (vwap_by_market_c_14 record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (reserved_1 record) = 1 /\
      Datatypes.length (second_unit_flag record) = 1 /\
      Datatypes.length (day_on_day_comparison_c_14 record) = 14 /\
      Datatypes.length (second_sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (vwap_by_market_c_14 record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 1 (reserved_1 record) ++
      encode_bytes 1 (second_unit_flag record) ++
      encode_bytes 14 (day_on_day_comparison_c_14 record) ++
      encode_bytes 1 (second_sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (vwap_by_market_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (second_unit_flag_value, bytes) =>
                          match decode_bytes 14 bytes with
                          | None => None
                          | Some (day_on_day_comparison_c_14_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (second_sign_value, bytes) =>
                                  Some ({| unit_flag := unit_flag_value; vwap_by_market_c_14 := vwap_by_market_c_14_value; sign := sign_value; reserved_1 := reserved_1_value; second_unit_flag := second_unit_flag_value; day_on_day_comparison_c_14 := day_on_day_comparison_c_14_value; second_sign := second_sign_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End VwapByMarket.

  Module VwapByMarketMessage.

    (** In this tag, volume weighted average price (VWAP) information for each market (issue classification) will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      issue_classification_code : list byte;
      vwap_by_market : VwapByMarket.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Datatypes.length (issue_classification_code record) = 4 /\
      VwapByMarket.bounded (vwap_by_market record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      encode_bytes 4 (issue_classification_code record) ++
      VwapByMarket.encode (vwap_by_market record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (issue_classification_code_value, bytes) =>
                  match VwapByMarket.decode bytes with
                  | None => None
                  | Some (vwap_by_market_value, bytes) =>
                      Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; issue_classification_code := issue_classification_code_value; vwap_by_market := vwap_by_market_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !VwapByMarket.encode_length. reflexivity.
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
      rewrite VwapByMarket.decode_encode by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply VwapByMarket.eq_dec]. Defined.

  End VwapByMarketMessage.

  Module TradingVolume.

    (** Trading volume *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      single_issue_transaction_c_14 : list byte;
      second_trading_volume_turnover_unit_flag : list byte;
      closing_price_transaction : list byte;
      third_trading_volume_turnover_unit_flag : list byte;
      basket_transaction_c_14 : list byte;
      fourth_trading_volume_turnover_unit_flag : list byte;
      aggregate_trading_volume : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (single_issue_transaction_c_14 record) = 14 /\
      Datatypes.length (second_trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (closing_price_transaction record) = 14 /\
      Datatypes.length (third_trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (basket_transaction_c_14 record) = 14 /\
      Datatypes.length (fourth_trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (aggregate_trading_volume record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (single_issue_transaction_c_14 record) ++
      encode_bytes 1 (second_trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (closing_price_transaction record) ++
      encode_bytes 1 (third_trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (basket_transaction_c_14 record) ++
      encode_bytes 1 (fourth_trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (aggregate_trading_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (single_issue_transaction_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (second_trading_volume_turnover_unit_flag_value, bytes) =>
                  match decode_bytes 14 bytes with
                  | None => None
                  | Some (closing_price_transaction_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (third_trading_volume_turnover_unit_flag_value, bytes) =>
                          match decode_bytes 14 bytes with
                          | None => None
                          | Some (basket_transaction_c_14_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (fourth_trading_volume_turnover_unit_flag_value, bytes) =>
                                  match decode_bytes 14 bytes with
                                  | None => None
                                  | Some (aggregate_trading_volume_value, bytes) =>
                                      Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; single_issue_transaction_c_14 := single_issue_transaction_c_14_value; second_trading_volume_turnover_unit_flag := second_trading_volume_turnover_unit_flag_value; closing_price_transaction := closing_price_transaction_value; third_trading_volume_turnover_unit_flag := third_trading_volume_turnover_unit_flag_value; basket_transaction_c_14 := basket_transaction_c_14_value; fourth_trading_volume_turnover_unit_flag := fourth_trading_volume_turnover_unit_flag_value; aggregate_trading_volume := aggregate_trading_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingVolume.

  Module Turnover.

    (** Turnover *)
    Record t := {
      trading_volume_turnover_unit_flag : list byte;
      single_issue_transaction_c_14 : list byte;
      second_trading_volume_turnover_unit_flag : list byte;
      closing_price_transaction : list byte;
      third_trading_volume_turnover_unit_flag : list byte;
      basket_transaction_c_14 : list byte;
      fourth_trading_volume_turnover_unit_flag : list byte;
      aggregate_turnover : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (single_issue_transaction_c_14 record) = 14 /\
      Datatypes.length (second_trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (closing_price_transaction record) = 14 /\
      Datatypes.length (third_trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (basket_transaction_c_14 record) = 14 /\
      Datatypes.length (fourth_trading_volume_turnover_unit_flag record) = 1 /\
      Datatypes.length (aggregate_turnover record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (single_issue_transaction_c_14 record) ++
      encode_bytes 1 (second_trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (closing_price_transaction record) ++
      encode_bytes 1 (third_trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (basket_transaction_c_14 record) ++
      encode_bytes 1 (fourth_trading_volume_turnover_unit_flag record) ++
      encode_bytes 14 (aggregate_turnover record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_volume_turnover_unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (single_issue_transaction_c_14_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (second_trading_volume_turnover_unit_flag_value, bytes) =>
                  match decode_bytes 14 bytes with
                  | None => None
                  | Some (closing_price_transaction_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (third_trading_volume_turnover_unit_flag_value, bytes) =>
                          match decode_bytes 14 bytes with
                          | None => None
                          | Some (basket_transaction_c_14_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (fourth_trading_volume_turnover_unit_flag_value, bytes) =>
                                  match decode_bytes 14 bytes with
                                  | None => None
                                  | Some (aggregate_turnover_value, bytes) =>
                                      Some ({| trading_volume_turnover_unit_flag := trading_volume_turnover_unit_flag_value; single_issue_transaction_c_14 := single_issue_transaction_c_14_value; second_trading_volume_turnover_unit_flag := second_trading_volume_turnover_unit_flag_value; closing_price_transaction := closing_price_transaction_value; third_trading_volume_turnover_unit_flag := third_trading_volume_turnover_unit_flag_value; basket_transaction_c_14 := basket_transaction_c_14_value; fourth_trading_volume_turnover_unit_flag := fourth_trading_volume_turnover_unit_flag_value; aggregate_turnover := aggregate_turnover_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Turnover.

  Module NumberOfTransactions.

    (** Number of transactions *)
    Record t := {
      single_issue_transaction_c_8 : list byte;
      basket_transaction_c_8 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (single_issue_transaction_c_8 record) = 8 /\
      Datatypes.length (basket_transaction_c_8 record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (single_issue_transaction_c_8 record) ++
      encode_bytes 8 (basket_transaction_c_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (single_issue_transaction_c_8_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (basket_transaction_c_8_value, bytes) =>
              Some ({| single_issue_transaction_c_8 := single_issue_transaction_c_8_value; basket_transaction_c_8 := basket_transaction_c_8_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NumberOfTransactions.

  Module ToSTNeTStatisticsMessage.

    (** In this tag, the quantities traded on the ToSTNeT and other information will be set. This data appears as part of a statistics message. *)
    Record t := {
      reserved_2 : list byte;
      output_time : list byte;
      other_classification_flag : list byte;
      trading_volume : TradingVolume.t;
      turnover : Turnover.t;
      number_of_transactions : NumberOfTransactions.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (output_time record) = 6 /\
      Datatypes.length (other_classification_flag record) = 2 /\
      TradingVolume.bounded (trading_volume record) /\
      Turnover.bounded (turnover record) /\
      NumberOfTransactions.bounded (number_of_transactions record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 6 (output_time record) ++
      encode_bytes 2 (other_classification_flag record) ++
      TradingVolume.encode (trading_volume record) ++
      Turnover.encode (turnover record) ++
      NumberOfTransactions.encode (number_of_transactions record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (output_time_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (other_classification_flag_value, bytes) =>
                  match TradingVolume.decode bytes with
                  | None => None
                  | Some (trading_volume_value, bytes) =>
                      match Turnover.decode bytes with
                      | None => None
                      | Some (turnover_value, bytes) =>
                          match NumberOfTransactions.decode bytes with
                          | None => None
                          | Some (number_of_transactions_value, bytes) =>
                              Some ({| reserved_2 := reserved_2_value; output_time := output_time_value; other_classification_flag := other_classification_flag_value; trading_volume := trading_volume_value; turnover := turnover_value; number_of_transactions := number_of_transactions_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 146.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !TradingVolume.encode_length, !Turnover.encode_length, !NumberOfTransactions.encode_length. reflexivity.
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
      rewrite TradingVolume.decode_encode by exact bound_3.
      rewrite Turnover.decode_encode by exact bound_4.
      rewrite NumberOfTransactions.decode_encode by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TradingVolume.eq_dec | apply Turnover.eq_dec | apply NumberOfTransactions.eq_dec]. Defined.

  End ToSTNeTStatisticsMessage.

  Module Open.

    (** Open *)
    Record t := {
      unit_flag : list byte;
      index_value : list byte;
      sign : list byte;
      time_c_6_hhmmss : list byte;
      flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (index_value record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_6_hhmmss record) = 6 /\
      Datatypes.length (flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (index_value record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 6 (time_c_6_hhmmss record) ++
      encode_bytes 1 (flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (index_value_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_hhmmss_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (flag_value, bytes) =>
                          Some ({| unit_flag := unit_flag_value; index_value := index_value_value; sign := sign_value; time_c_6_hhmmss := time_c_6_hhmmss_value; flag := flag_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Open.

  Module Highest.

    (** Highest *)
    Record t := {
      unit_flag : list byte;
      index_value : list byte;
      sign : list byte;
      time_c_6_hhmmss : list byte;
      flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (index_value record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_6_hhmmss record) = 6 /\
      Datatypes.length (flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (index_value record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 6 (time_c_6_hhmmss record) ++
      encode_bytes 1 (flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (index_value_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_hhmmss_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (flag_value, bytes) =>
                          Some ({| unit_flag := unit_flag_value; index_value := index_value_value; sign := sign_value; time_c_6_hhmmss := time_c_6_hhmmss_value; flag := flag_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Highest.

  Module Lowest.

    (** Lowest *)
    Record t := {
      unit_flag : list byte;
      index_value : list byte;
      sign : list byte;
      time_c_6_hhmmss : list byte;
      flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (index_value record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_6_hhmmss record) = 6 /\
      Datatypes.length (flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (index_value record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 6 (time_c_6_hhmmss record) ++
      encode_bytes 1 (flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (index_value_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_hhmmss_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (flag_value, bytes) =>
                          Some ({| unit_flag := unit_flag_value; index_value := index_value_value; sign := sign_value; time_c_6_hhmmss := time_c_6_hhmmss_value; flag := flag_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Lowest.

  Module CurrentPrice.

    (** Current price *)
    Record t := {
      unit_flag : list byte;
      index_value : list byte;
      sign : list byte;
      time_c_6_hhmmss : list byte;
      flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (index_value record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_6_hhmmss record) = 6 /\
      Datatypes.length (flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (index_value record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 6 (time_c_6_hhmmss record) ++
      encode_bytes 1 (flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (index_value_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_hhmmss_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (flag_value, bytes) =>
                          Some ({| unit_flag := unit_flag_value; index_value := index_value_value; sign := sign_value; time_c_6_hhmmss := time_c_6_hhmmss_value; flag := flag_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CurrentPrice.

  Module IndexDayOnDayComparison.

    (** Index Day-on-day comparison *)
    Record t := {
      net_change_rate : list byte;
      sign : list byte;
      unit_flag : list byte;
      net_change : list byte;
      second_sign : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (net_change_rate record) = 8 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (net_change record) = 14 /\
      Datatypes.length (second_sign record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (net_change_rate record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (net_change record) ++
      encode_bytes 1 (second_sign record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (net_change_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (sign_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (unit_flag_value, bytes) =>
                  match decode_bytes 14 bytes with
                  | None => None
                  | Some (net_change_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (second_sign_value, bytes) =>
                          Some ({| net_change_rate := net_change_rate_value; sign := sign_value; unit_flag := unit_flag_value; net_change := net_change_value; second_sign := second_sign_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexDayOnDayComparison.

  Module IndexOpenHighLowAndClosingPricesMessage.

    (** In this tag, index information will be set. This data is appeared as one of index data. *)
    Record t := {
      reserved_2 : list byte;
      index_type : list byte;
      open : Open.t;
      highest : Highest.t;
      lowest : Lowest.t;
      current_price : CurrentPrice.t;
      index_day_on_day_comparison : IndexDayOnDayComparison.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (index_type record) = 4 /\
      Open.bounded (open record) /\
      Highest.bounded (highest record) /\
      Lowest.bounded (lowest record) /\
      CurrentPrice.bounded (current_price record) /\
      IndexDayOnDayComparison.bounded (index_day_on_day_comparison record).

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 4 (index_type record) ++
      Open.encode (open record) ++
      Highest.encode (highest record) ++
      Lowest.encode (lowest record) ++
      CurrentPrice.encode (current_price record) ++
      IndexDayOnDayComparison.encode (index_day_on_day_comparison record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (index_type_value, bytes) =>
              match Open.decode bytes with
              | None => None
              | Some (open_value, bytes) =>
                  match Highest.decode bytes with
                  | None => None
                  | Some (highest_value, bytes) =>
                      match Lowest.decode bytes with
                      | None => None
                      | Some (lowest_value, bytes) =>
                          match CurrentPrice.decode bytes with
                          | None => None
                          | Some (current_price_value, bytes) =>
                              match IndexDayOnDayComparison.decode bytes with
                              | None => None
                              | Some (index_day_on_day_comparison_value, bytes) =>
                                  Some ({| reserved_2 := reserved_2_value; index_type := index_type_value; open := open_value; highest := highest_value; lowest := lowest_value; current_price := current_price_value; index_day_on_day_comparison := index_day_on_day_comparison_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 123.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Open.encode_length, !Highest.encode_length, !Lowest.encode_length, !CurrentPrice.encode_length, !IndexDayOnDayComparison.encode_length. reflexivity.
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
      rewrite Open.decode_encode by exact bound_2.
      rewrite Highest.decode_encode by exact bound_3.
      rewrite Lowest.decode_encode by exact bound_4.
      rewrite CurrentPrice.decode_encode by exact bound_5.
      rewrite IndexDayOnDayComparison.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Open.eq_dec | apply Highest.eq_dec | apply Lowest.eq_dec | apply CurrentPrice.eq_dec | apply IndexDayOnDayComparison.eq_dec]. Defined.

  End IndexOpenHighLowAndClosingPricesMessage.

  Module Index.

    (** Index *)
    Record t := {
      unit_flag : list byte;
      index_value : list byte;
      sign : list byte;
      time_c_6_hhmmss : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (unit_flag record) = 1 /\
      Datatypes.length (index_value record) = 14 /\
      Datatypes.length (sign record) = 1 /\
      Datatypes.length (time_c_6_hhmmss record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (unit_flag record) ++
      encode_bytes 14 (index_value record) ++
      encode_bytes 1 (sign record) ++
      encode_bytes 6 (time_c_6_hhmmss record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (unit_flag_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (index_value_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sign_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_hhmmss_value, bytes) =>
                      Some ({| unit_flag := unit_flag_value; index_value := index_value_value; sign := sign_value; time_c_6_hhmmss := time_c_6_hhmmss_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Index.

  Module SpecialQuotationMessage.

    (** In this tag, special quotation (S.Q.) information will be set. This data appears as part of index data. *)
    Record t := {
      reserved_2 : list byte;
      sq_type : list byte;
      index : Index.t;
      reserved_1 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (sq_type record) = 4 /\
      Index.bounded (index record) /\
      Datatypes.length (reserved_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 4 (sq_type record) ++
      Index.encode (index record) ++
      encode_bytes 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 4 bytes with
          | None => None
          | Some (sq_type_value, bytes) =>
              match Index.decode bytes with
              | None => None
              | Some (index_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      Some ({| reserved_2 := reserved_2_value; sq_type := sq_type_value; index := index_value; reserved_1 := reserved_1_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !Index.encode_length. reflexivity.
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
      rewrite Index.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Index.eq_dec]. Defined.

  End SpecialQuotationMessage.

  Module ControlMessage.

    (** In this tag, the test mode flag and the start/end flag that are used in a control message will be set. This tag will be edited into a control message (communication control and health check control) for output. *)
    Record t := {
      reserved_2 : list byte;
      test_mode_flag : list byte;
      startend_flag : list byte;
      time_c_6_hhmm : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved_2 record) = 2 /\
      Datatypes.length (test_mode_flag record) = 1 /\
      Datatypes.length (startend_flag record) = 1 /\
      Datatypes.length (time_c_6_hhmm record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (reserved_2 record) ++
      encode_bytes 1 (test_mode_flag record) ++
      encode_bytes 1 (startend_flag record) ++
      encode_bytes 6 (time_c_6_hhmm record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (reserved_2_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (test_mode_flag_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (startend_flag_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (time_c_6_hhmm_value, bytes) =>
                      Some ({| reserved_2 := reserved_2_value; test_mode_flag := test_mode_flag_value; startend_flag := startend_flag_value; time_c_6_hhmm := time_c_6_hhmm_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ControlMessage.

End TseEquitiesIndexStatisticsV195.
