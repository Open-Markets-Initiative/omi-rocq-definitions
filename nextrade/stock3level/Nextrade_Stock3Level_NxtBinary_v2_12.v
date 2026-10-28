From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Nextrade Nextrade Stock Market Data 3 Level

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

Module NextradeStock3LevelV212.

  Module PollingDataMessage.

    (** The data is provided periodically in order to check multicast group status. *)
    Record t := {
      current_time_1_minute_interval : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (current_time_1_minute_interval record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (current_time_1_minute_interval record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (current_time_1_minute_interval_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (end_keyword_value, bytes) =>
              Some ({| current_time_1_minute_interval := current_time_1_minute_interval_value; end_keyword := end_keyword_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  Module SecuritiesQuote3LevelMessage.

    (** Securities_Quote(MM/LP Quotes Excluded) Best Order Data on NXT Trading Items provided - MM/LP Quotes Excluded * 3 Level Best Order on Ask/Bid. *)
    Record t := {
      message_sequence_number : N;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : N;
      processing_time_of_trading_system : list byte;
      ask_level_1_price : N;
      bid_level_1_price : N;
      ask_level_1_volume : N;
      bid_level_1_volume : N;
      ask_level_2_price : N;
      bid_level_2_price : N;
      ask_level_2_volume : N;
      bid_level_2_volume : N;
      ask_level_3_price : N;
      bid_level_3_price : N;
      ask_level_3_volume : N;
      bid_level_3_volume : N;
      total_ask_volume_level_10 : N;
      total_bid_volume_level_10 : N;
      estimated_trading_price : N;
      estimated_trading_volume : N;
      mid_price : N;
      total_mid_price_ask_volume_total_ask_volume_on_mid_price : N;
      total_mid_price_bid_volume_total_bid_volume_on_mid_price : N;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      (a_designated_number_for_an_issue_from_krx record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      (ask_level_1_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_1_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_1_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_1_volume record < 256 ^ N.of_nat 8)%N /\
      (ask_level_2_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_2_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_2_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_2_volume record < 256 ^ N.of_nat 8)%N /\
      (ask_level_3_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_3_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_3_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_3_volume record < 256 ^ N.of_nat 8)%N /\
      (total_ask_volume_level_10 record < 256 ^ N.of_nat 8)%N /\
      (total_bid_volume_level_10 record < 256 ^ N.of_nat 8)%N /\
      (estimated_trading_price record < 256 ^ N.of_nat 8)%N /\
      (estimated_trading_volume record < 256 ^ N.of_nat 8)%N /\
      (mid_price record < 256 ^ N.of_nat 8)%N /\
      (total_mid_price_ask_volume_total_ask_volume_on_mid_price record < 256 ^ N.of_nat 8)%N /\
      (total_mid_price_bid_volume_total_bid_volume_on_mid_price record < 256 ^ N.of_nat 8)%N /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 4 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_uint 8 (ask_level_1_price record) ++
      encode_uint 8 (bid_level_1_price record) ++
      encode_uint 8 (ask_level_1_volume record) ++
      encode_uint 8 (bid_level_1_volume record) ++
      encode_uint 8 (ask_level_2_price record) ++
      encode_uint 8 (bid_level_2_price record) ++
      encode_uint 8 (ask_level_2_volume record) ++
      encode_uint 8 (bid_level_2_volume record) ++
      encode_uint 8 (ask_level_3_price record) ++
      encode_uint 8 (bid_level_3_price record) ++
      encode_uint 8 (ask_level_3_volume record) ++
      encode_uint 8 (bid_level_3_volume record) ++
      encode_uint 8 (total_ask_volume_level_10 record) ++
      encode_uint 8 (total_bid_volume_level_10 record) ++
      encode_uint 8 (estimated_trading_price record) ++
      encode_uint 8 (estimated_trading_volume record) ++
      encode_uint 8 (mid_price record) ++
      encode_uint 8 (total_mid_price_ask_volume_total_ask_volume_on_mid_price record) ++
      encode_uint 8 (total_mid_price_bid_volume_total_bid_volume_on_mid_price record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (ask_level_1_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (bid_level_1_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (ask_level_1_volume_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (bid_level_1_volume_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (ask_level_2_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (bid_level_2_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (ask_level_2_volume_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (bid_level_2_volume_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (ask_level_3_price_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (bid_level_3_price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_3_volume_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_3_volume_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (total_ask_volume_level_10_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (total_bid_volume_level_10_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (estimated_trading_price_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (estimated_trading_volume_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (mid_price_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (total_mid_price_ask_volume_total_ask_volume_on_mid_price_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (total_mid_price_bid_volume_total_bid_volume_on_mid_price_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; total_ask_volume_level_10 := total_ask_volume_level_10_value; total_bid_volume_level_10 := total_bid_volume_level_10_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; mid_price := mid_price_value; total_mid_price_ask_volume_total_ask_volume_on_mid_price := total_mid_price_ask_volume_total_ask_volume_on_mid_price_value; total_mid_price_bid_volume_total_bid_volume_on_mid_price := total_mid_price_bid_volume_total_bid_volume_on_mid_price_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesQuote3LevelMessage.

  Module SecuritiesOrderFilledPlusQuote3LevelMessage.

    (** Securities_Order Filled With Quote Order Filled data with Best Order on NXT trading items - MM/LP Quotes Excluded * 3 Level Best Order on Ask/Bid. *)
    Record t := {
      message_sequence_number : N;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : N;
      processing_time_of_trading_system : list byte;
      price_change_against_previous_day : list byte;
      a_price_change_against_the_previous_day : N;
      trading_price : N;
      trading_volume : N;
      opening_price : N;
      todays_high : N;
      todays_low : N;
      accumulated_trading_volume : N;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      lp_holding_quantity : N;
      ask_level_1_price : N;
      bid_level_1_price : N;
      ask_level_1_volume : N;
      bid_level_1_volume : N;
      ask_level_2_price : N;
      bid_level_2_price : N;
      ask_level_2_volume : N;
      bid_level_2_volume : N;
      ask_level_3_price : N;
      bid_level_3_price : N;
      ask_level_3_volume : N;
      bid_level_3_volume : N;
      total_ask_volume_level_10 : N;
      total_bid_volume_level_10 : N;
      mid_price : N;
      total_mid_price_ask_volume_total_ask_volume_on_mid_price : N;
      total_mid_price_bid_volume_total_bid_volume_on_mid_price : N;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      (a_designated_number_for_an_issue_from_krx record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (price_change_against_previous_day record) = 1 /\
      (a_price_change_against_the_previous_day record < 256 ^ N.of_nat 8)%N /\
      (trading_price record < 256 ^ N.of_nat 8)%N /\
      (trading_volume record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (todays_high record < 256 ^ N.of_nat 8)%N /\
      (todays_low record < 256 ^ N.of_nat 8)%N /\
      (accumulated_trading_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (accumulated_trading_value record) = 16 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      (lp_holding_quantity record < 256 ^ N.of_nat 8)%N /\
      (ask_level_1_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_1_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_1_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_1_volume record < 256 ^ N.of_nat 8)%N /\
      (ask_level_2_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_2_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_2_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_2_volume record < 256 ^ N.of_nat 8)%N /\
      (ask_level_3_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_3_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_3_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_3_volume record < 256 ^ N.of_nat 8)%N /\
      (total_ask_volume_level_10 record < 256 ^ N.of_nat 8)%N /\
      (total_bid_volume_level_10 record < 256 ^ N.of_nat 8)%N /\
      (mid_price record < 256 ^ N.of_nat 8)%N /\
      (total_mid_price_ask_volume_total_ask_volume_on_mid_price record < 256 ^ N.of_nat 8)%N /\
      (total_mid_price_bid_volume_total_bid_volume_on_mid_price record < 256 ^ N.of_nat 8)%N /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 4 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 1 (price_change_against_previous_day record) ++
      encode_uint 8 (a_price_change_against_the_previous_day record) ++
      encode_uint 8 (trading_price record) ++
      encode_uint 8 (trading_volume record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (todays_high record) ++
      encode_uint 8 (todays_low record) ++
      encode_uint 8 (accumulated_trading_volume record) ++
      encode_bytes 16 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_uint 8 (lp_holding_quantity record) ++
      encode_uint 8 (ask_level_1_price record) ++
      encode_uint 8 (bid_level_1_price record) ++
      encode_uint 8 (ask_level_1_volume record) ++
      encode_uint 8 (bid_level_1_volume record) ++
      encode_uint 8 (ask_level_2_price record) ++
      encode_uint 8 (bid_level_2_price record) ++
      encode_uint 8 (ask_level_2_volume record) ++
      encode_uint 8 (bid_level_2_volume record) ++
      encode_uint 8 (ask_level_3_price record) ++
      encode_uint 8 (bid_level_3_price record) ++
      encode_uint 8 (ask_level_3_volume record) ++
      encode_uint 8 (bid_level_3_volume record) ++
      encode_uint 8 (total_ask_volume_level_10 record) ++
      encode_uint 8 (total_bid_volume_level_10 record) ++
      encode_uint 8 (mid_price record) ++
      encode_uint 8 (total_mid_price_ask_volume_total_ask_volume_on_mid_price record) ++
      encode_uint 8 (total_mid_price_bid_volume_total_bid_volume_on_mid_price record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (price_change_against_previous_day_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (a_price_change_against_the_previous_day_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trading_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trading_volume_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (opening_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (todays_high_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (todays_low_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_volume_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (accumulated_trading_value_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (final_ask_bid_type_code_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (lp_holding_quantity_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (ask_level_1_price_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (bid_level_1_price_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_1_volume_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_1_volume_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_2_volume_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_2_volume_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_3_price_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_3_price_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_3_volume_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (total_ask_volume_level_10_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (total_bid_volume_level_10_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (mid_price_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (total_mid_price_ask_volume_total_ask_volume_on_mid_price_value, bytes) =>
                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (total_mid_price_bid_volume_total_bid_volume_on_mid_price_value, bytes) =>
                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; processing_time_of_trading_system := processing_time_of_trading_system_value; price_change_against_previous_day := price_change_against_previous_day_value; a_price_change_against_the_previous_day := a_price_change_against_the_previous_day_value; trading_price := trading_price_value; trading_volume := trading_volume_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; lp_holding_quantity := lp_holding_quantity_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; total_ask_volume_level_10 := total_ask_volume_level_10_value; total_bid_volume_level_10 := total_bid_volume_level_10_value; mid_price := mid_price_value; total_mid_price_ask_volume_total_ask_volume_on_mid_price := total_mid_price_ask_volume_total_ask_volume_on_mid_price_value; total_mid_price_bid_volume_total_bid_volume_on_mid_price := total_mid_price_bid_volume_total_bid_volume_on_mid_price_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 258.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 bound_34]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesOrderFilledPlusQuote3LevelMessage.

  Module MarketOperationTsPlusQuote3LevelMessage.

    (** Market Operation TS with Best Order on NXT trading items - MM/LP Quotes Excluded The data is provided per an issue if a Market Operation Trading session event occurs and Best Order changes. * 3 Level. *)
    Record t := {
      message_sequence_number : N;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : N;
      processing_time_of_trading_system : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : N;
      trading_halt_reason_code : list byte;
      ask_level_1_price : N;
      bid_level_1_price : N;
      ask_level_1_volume : N;
      bid_level_1_volume : N;
      ask_level_2_price : N;
      bid_level_2_price : N;
      ask_level_2_volume : N;
      bid_level_2_volume : N;
      ask_level_3_price : N;
      bid_level_3_price : N;
      ask_level_3_volume : N;
      bid_level_3_volume : N;
      total_ask_volume_level_10 : N;
      total_bid_volume_level_10 : N;
      estimated_trading_price : N;
      estimated_trading_volume : N;
      mid_price : N;
      total_mid_price_ask_volume_total_ask_volume_on_mid_price : N;
      total_mid_price_bid_volume_total_bid_volume_on_mid_price : N;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      (a_designated_number_for_an_issue_from_krx record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      (board_event_group_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      (ask_level_1_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_1_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_1_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_1_volume record < 256 ^ N.of_nat 8)%N /\
      (ask_level_2_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_2_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_2_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_2_volume record < 256 ^ N.of_nat 8)%N /\
      (ask_level_3_price record < 256 ^ N.of_nat 8)%N /\
      (bid_level_3_price record < 256 ^ N.of_nat 8)%N /\
      (ask_level_3_volume record < 256 ^ N.of_nat 8)%N /\
      (bid_level_3_volume record < 256 ^ N.of_nat 8)%N /\
      (total_ask_volume_level_10 record < 256 ^ N.of_nat 8)%N /\
      (total_bid_volume_level_10 record < 256 ^ N.of_nat 8)%N /\
      (estimated_trading_price record < 256 ^ N.of_nat 8)%N /\
      (estimated_trading_volume record < 256 ^ N.of_nat 8)%N /\
      (mid_price record < 256 ^ N.of_nat 8)%N /\
      (total_mid_price_ask_volume_total_ask_volume_on_mid_price record < 256 ^ N.of_nat 8)%N /\
      (total_mid_price_bid_volume_total_bid_volume_on_mid_price record < 256 ^ N.of_nat 8)%N /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 4 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_uint 4 (board_event_group_code record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_uint 8 (ask_level_1_price record) ++
      encode_uint 8 (bid_level_1_price record) ++
      encode_uint 8 (ask_level_1_volume record) ++
      encode_uint 8 (bid_level_1_volume record) ++
      encode_uint 8 (ask_level_2_price record) ++
      encode_uint 8 (bid_level_2_price record) ++
      encode_uint 8 (ask_level_2_volume record) ++
      encode_uint 8 (bid_level_2_volume record) ++
      encode_uint 8 (ask_level_3_price record) ++
      encode_uint 8 (bid_level_3_price record) ++
      encode_uint 8 (ask_level_3_volume record) ++
      encode_uint 8 (bid_level_3_volume record) ++
      encode_uint 8 (total_ask_volume_level_10 record) ++
      encode_uint 8 (total_bid_volume_level_10 record) ++
      encode_uint 8 (estimated_trading_price record) ++
      encode_uint 8 (estimated_trading_volume record) ++
      encode_uint 8 (mid_price record) ++
      encode_uint 8 (total_mid_price_ask_volume_total_ask_volume_on_mid_price record) ++
      encode_uint 8 (total_mid_price_bid_volume_total_bid_volume_on_mid_price record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (board_event_id_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (start_time_of_a_board_event_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (board_event_group_code_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (trading_halt_reason_code_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (ask_level_1_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (bid_level_1_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (ask_level_1_volume_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (bid_level_1_volume_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (ask_level_2_price_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (bid_level_2_price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_2_volume_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_2_volume_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_3_price_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_3_price_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_level_3_volume_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_level_3_volume_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (total_ask_volume_level_10_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (total_bid_volume_level_10_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (estimated_trading_price_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (estimated_trading_volume_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (mid_price_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (total_mid_price_ask_volume_total_ask_volume_on_mid_price_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (total_mid_price_bid_volume_total_bid_volume_on_mid_price_value, bytes) =>
                                                                                                                          match decode_uint 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; processing_time_of_trading_system := processing_time_of_trading_system_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; trading_halt_reason_code := trading_halt_reason_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; total_ask_volume_level_10 := total_ask_volume_level_10_value; total_bid_volume_level_10 := total_bid_volume_level_10_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; mid_price := mid_price_value; total_mid_price_ask_volume_total_ask_volume_on_mid_price := total_mid_price_ask_volume_total_ask_volume_on_mid_price_value; total_mid_price_bid_volume_total_bid_volume_on_mid_price := total_mid_price_bid_volume_total_bid_volume_on_mid_price_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 211.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 bound_29]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketOperationTsPlusQuote3LevelMessage.

  Module SecuritiesOrderFilledMessage.

    (** Securities_Order Filled Order Filled Data on NXT trading items provided. *)
    Record t := {
      message_sequence_number : N;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : N;
      processing_time_of_trading_system : list byte;
      price_change_against_previous_day : list byte;
      a_price_change_against_the_previous_day : N;
      trading_price : N;
      trading_volume : N;
      opening_price : N;
      todays_high : N;
      todays_low : N;
      accumulated_trading_volume : N;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      lp_holding_quantity : N;
      the_best_ask : N;
      the_best_bid : N;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      (a_designated_number_for_an_issue_from_krx record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (price_change_against_previous_day record) = 1 /\
      (a_price_change_against_the_previous_day record < 256 ^ N.of_nat 8)%N /\
      (trading_price record < 256 ^ N.of_nat 8)%N /\
      (trading_volume record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (todays_high record < 256 ^ N.of_nat 8)%N /\
      (todays_low record < 256 ^ N.of_nat 8)%N /\
      (accumulated_trading_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (accumulated_trading_value record) = 16 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      (lp_holding_quantity record < 256 ^ N.of_nat 8)%N /\
      (the_best_ask record < 256 ^ N.of_nat 8)%N /\
      (the_best_bid record < 256 ^ N.of_nat 8)%N /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 4 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 1 (price_change_against_previous_day record) ++
      encode_uint 8 (a_price_change_against_the_previous_day record) ++
      encode_uint 8 (trading_price record) ++
      encode_uint 8 (trading_volume record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (todays_high record) ++
      encode_uint 8 (todays_low record) ++
      encode_uint 8 (accumulated_trading_volume record) ++
      encode_bytes 16 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_uint 8 (lp_holding_quantity record) ++
      encode_uint 8 (the_best_ask record) ++
      encode_uint 8 (the_best_bid record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (price_change_against_previous_day_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (a_price_change_against_the_previous_day_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (trading_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trading_volume_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (opening_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (todays_high_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (todays_low_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_volume_value, bytes) =>
                                                              match decode_bytes 16 bytes with
                                                              | None => None
                                                              | Some (accumulated_trading_value_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (final_ask_bid_type_code_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (lp_holding_quantity_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (the_best_ask_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (the_best_bid_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; processing_time_of_trading_system := processing_time_of_trading_system_value; price_change_against_previous_day := price_change_against_previous_day_value; a_price_change_against_the_previous_day := a_price_change_against_the_previous_day_value; trading_price := trading_price_value; trading_volume := trading_volume_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; lp_holding_quantity := lp_holding_quantity_value; the_best_ask := the_best_ask_value; the_best_bid := the_best_bid_value; end_keyword := end_keyword_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesOrderFilledMessage.

  Module MarketOperationTsMessage.

    (** The data is provided per an issue if a Market Operation Trading session event occurs. *)
    Record t := {
      message_sequence_number : N;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : N;
      processing_time_of_trading_system : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : N;
      trading_halt_reason_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      (a_designated_number_for_an_issue_from_krx record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      (board_event_group_code record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 4 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_uint 4 (board_event_group_code record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
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
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (processing_time_of_trading_system_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (board_event_id_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (start_time_of_a_board_event_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (board_event_group_code_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (trading_halt_reason_code_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (end_keyword_value, bytes) =>
                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; processing_time_of_trading_system := processing_time_of_trading_system_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; trading_halt_reason_code := trading_halt_reason_code_value; end_keyword := end_keyword_value |}, bytes)
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketOperationTsMessage.

  Module IssueClosingMessage.

    (** The data is provided in case of an issue closing per board. *)
    Record t := {
      message_sequence_number : N;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : N;
      closing_price : N;
      closing_price_type_code : list byte;
      upper_limit_price_on_the_single_price_trade_in_the_off_hours_session : N;
      lower_limit_price_on_the_single_price_trade_in_the_off_hours_session : N;
      closing_price_weighted_stock_price_average : N;
      closing_price_base_price_of_buy_in : N;
      closing_price_upper_limit_of_buy_in : N;
      closing_price_lower_limit_of_buy_in : N;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      (a_designated_number_for_an_issue_from_krx record < 256 ^ N.of_nat 4)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (closing_price_type_code record) = 1 /\
      (upper_limit_price_on_the_single_price_trade_in_the_off_hours_session record < 256 ^ N.of_nat 8)%N /\
      (lower_limit_price_on_the_single_price_trade_in_the_off_hours_session record < 256 ^ N.of_nat 8)%N /\
      (closing_price_weighted_stock_price_average record < 256 ^ N.of_nat 8)%N /\
      (closing_price_base_price_of_buy_in record < 256 ^ N.of_nat 8)%N /\
      (closing_price_upper_limit_of_buy_in record < 256 ^ N.of_nat 8)%N /\
      (closing_price_lower_limit_of_buy_in record < 256 ^ N.of_nat 8)%N /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 4 (a_designated_number_for_an_issue_from_krx record) ++
      encode_uint 8 (closing_price record) ++
      encode_bytes 1 (closing_price_type_code record) ++
      encode_uint 8 (upper_limit_price_on_the_single_price_trade_in_the_off_hours_session record) ++
      encode_uint 8 (lower_limit_price_on_the_single_price_trade_in_the_off_hours_session record) ++
      encode_uint 8 (closing_price_weighted_stock_price_average record) ++
      encode_uint 8 (closing_price_base_price_of_buy_in record) ++
      encode_uint 8 (closing_price_upper_limit_of_buy_in record) ++
      encode_uint 8 (closing_price_lower_limit_of_buy_in record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (closing_price_type_code_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (upper_limit_price_on_the_single_price_trade_in_the_off_hours_session_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (lower_limit_price_on_the_single_price_trade_in_the_off_hours_session_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (closing_price_weighted_stock_price_average_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (closing_price_base_price_of_buy_in_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (closing_price_upper_limit_of_buy_in_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (closing_price_lower_limit_of_buy_in_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (end_keyword_value, bytes) =>
                                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; closing_price := closing_price_value; closing_price_type_code := closing_price_type_code_value; upper_limit_price_on_the_single_price_trade_in_the_off_hours_session := upper_limit_price_on_the_single_price_trade_in_the_off_hours_session_value; lower_limit_price_on_the_single_price_trade_in_the_off_hours_session := lower_limit_price_on_the_single_price_trade_in_the_off_hours_session_value; closing_price_weighted_stock_price_average := closing_price_weighted_stock_price_average_value; closing_price_base_price_of_buy_in := closing_price_base_price_of_buy_in_value; closing_price_upper_limit_of_buy_in := closing_price_upper_limit_of_buy_in_value; closing_price_lower_limit_of_buy_in := closing_price_lower_limit_of_buy_in_value; end_keyword := end_keyword_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IssueClosingMessage.

  Module TriggeringRemovingViMessage.

    (** Triggering/removing VI (Volatility Interruption). *)
    Record t := {
      message_sequence_number : N;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : N;
      processing_time_of_trading_system : list byte;
      the_time_ending_vi : list byte;
      vi_status_code : list byte;
      vi_type_code : list byte;
      a_base_price_to_trigger_static_vi : N;
      a_base_price_to_trigger_dynamic_vi : N;
      vi_triggering_price : N;
      disparate_ratio_to_trigger_static_vi : N;
      disparate_ratio_to_trigger_dynamic_vi : N;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      (a_designated_number_for_an_issue_from_krx record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (the_time_ending_vi record) = 9 /\
      Datatypes.length (vi_status_code record) = 1 /\
      Datatypes.length (vi_type_code record) = 1 /\
      (a_base_price_to_trigger_static_vi record < 256 ^ N.of_nat 8)%N /\
      (a_base_price_to_trigger_dynamic_vi record < 256 ^ N.of_nat 8)%N /\
      (vi_triggering_price record < 256 ^ N.of_nat 8)%N /\
      (disparate_ratio_to_trigger_static_vi record < 256 ^ N.of_nat 8)%N /\
      (disparate_ratio_to_trigger_dynamic_vi record < 256 ^ N.of_nat 8)%N /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 4 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 9 (the_time_ending_vi record) ++
      encode_bytes 1 (vi_status_code record) ++
      encode_bytes 1 (vi_type_code record) ++
      encode_uint 8 (a_base_price_to_trigger_static_vi record) ++
      encode_uint 8 (a_base_price_to_trigger_dynamic_vi record) ++
      encode_uint 8 (vi_triggering_price record) ++
      encode_uint 8 (disparate_ratio_to_trigger_static_vi record) ++
      encode_uint 8 (disparate_ratio_to_trigger_dynamic_vi record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
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
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (a_base_price_to_trigger_static_vi_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (a_base_price_to_trigger_dynamic_vi_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (vi_triggering_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (disparate_ratio_to_trigger_static_vi_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (disparate_ratio_to_trigger_dynamic_vi_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (end_keyword_value, bytes) =>
                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; processing_time_of_trading_system := processing_time_of_trading_system_value; the_time_ending_vi := the_time_ending_vi_value; vi_status_code := vi_status_code_value; vi_type_code := vi_type_code_value; a_base_price_to_trigger_static_vi := a_base_price_to_trigger_static_vi_value; a_base_price_to_trigger_dynamic_vi := a_base_price_to_trigger_dynamic_vi_value; vi_triggering_price := vi_triggering_price_value; disparate_ratio_to_trigger_static_vi := disparate_ratio_to_trigger_static_vi_value; disparate_ratio_to_trigger_dynamic_vi := disparate_ratio_to_trigger_dynamic_vi_value; end_keyword := end_keyword_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 89.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TriggeringRemovingViMessage.

  Module ClosingPriceTradingQuoteMessage.

    (** Total Ask/Bid volume per Issue on Closing Price Trade. *)
    Record t := {
      message_sequence_number : N;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : N;
      total_ask_volume : N;
      total_bid_volume : N;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_sequence_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      (a_designated_number_for_an_issue_from_krx record < 256 ^ N.of_nat 4)%N /\
      (total_ask_volume record < 256 ^ N.of_nat 8)%N /\
      (total_bid_volume record < 256 ^ N.of_nat 8)%N /\
      (end_keyword record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 4 (a_designated_number_for_an_issue_from_krx record) ++
      encode_uint 8 (total_ask_volume record) ++
      encode_uint 8 (total_bid_volume record) ++
      encode_uint 4 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (total_ask_volume_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (total_bid_volume_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; end_keyword := end_keyword_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClosingPriceTradingQuoteMessage.

End NextradeStock3LevelV212.
