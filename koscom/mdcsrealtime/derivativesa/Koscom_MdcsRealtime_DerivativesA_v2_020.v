From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Koscom Co., Ltd. MDCS Realtime Derivatives A

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

Module KoscomMdcsRealtimeDerivativesAV2020.

  Module PollingDataMessage.

    (** Polling Data. Transmitted at one-minute intervals on every market data line, all markets, 24 hours a day. *)
    Record t := {
      current_time_1_minute_interval : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (current_time_1_minute_interval record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (current_time_1_minute_interval record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (current_time_1_minute_interval_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (end_keyword_value, bytes) =>
              Some ({| current_time_1_minute_interval := current_time_1_minute_interval_value; end_keyword := end_keyword_value |}, bytes)
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

  Module DerivativesQuoteFiveLevelsMessage.

    (** Derivatives Quote (Five levels). Multi-level bid/ask quotes for futures, options, and other derivatives. Five levels of depth. *)
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
      ask_level_1_order_counts : list byte;
      bid_level_1_order_counts : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_2_order_counts : list byte;
      bid_level_2_order_counts : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_3_order_counts : list byte;
      bid_level_3_order_counts : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_4_order_counts : list byte;
      bid_level_4_order_counts : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      ask_level_5_order_counts : list byte;
      bid_level_5_order_counts : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      ask_price_valid_counts : list byte;
      bid_price_valid_counts : list byte;
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
      Datatypes.length (ask_level_1_price record) = 9 /\
      Datatypes.length (bid_level_1_price record) = 9 /\
      Datatypes.length (ask_level_1_volume record) = 9 /\
      Datatypes.length (bid_level_1_volume record) = 9 /\
      Datatypes.length (ask_level_1_order_counts record) = 5 /\
      Datatypes.length (bid_level_1_order_counts record) = 5 /\
      Datatypes.length (ask_level_2_price record) = 9 /\
      Datatypes.length (bid_level_2_price record) = 9 /\
      Datatypes.length (ask_level_2_volume record) = 9 /\
      Datatypes.length (bid_level_2_volume record) = 9 /\
      Datatypes.length (ask_level_2_order_counts record) = 5 /\
      Datatypes.length (bid_level_2_order_counts record) = 5 /\
      Datatypes.length (ask_level_3_price record) = 9 /\
      Datatypes.length (bid_level_3_price record) = 9 /\
      Datatypes.length (ask_level_3_volume record) = 9 /\
      Datatypes.length (bid_level_3_volume record) = 9 /\
      Datatypes.length (ask_level_3_order_counts record) = 5 /\
      Datatypes.length (bid_level_3_order_counts record) = 5 /\
      Datatypes.length (ask_level_4_price record) = 9 /\
      Datatypes.length (bid_level_4_price record) = 9 /\
      Datatypes.length (ask_level_4_volume record) = 9 /\
      Datatypes.length (bid_level_4_volume record) = 9 /\
      Datatypes.length (ask_level_4_order_counts record) = 5 /\
      Datatypes.length (bid_level_4_order_counts record) = 5 /\
      Datatypes.length (ask_level_5_price record) = 9 /\
      Datatypes.length (bid_level_5_price record) = 9 /\
      Datatypes.length (ask_level_5_volume record) = 9 /\
      Datatypes.length (bid_level_5_volume record) = 9 /\
      Datatypes.length (ask_level_5_order_counts record) = 5 /\
      Datatypes.length (bid_level_5_order_counts record) = 5 /\
      Datatypes.length (ask_total_volume record) = 9 /\
      Datatypes.length (bid_total_volume record) = 9 /\
      Datatypes.length (ask_price_valid_counts record) = 5 /\
      Datatypes.length (bid_price_valid_counts record) = 5 /\
      Datatypes.length (estimated_trading_price record) = 9 /\
      Datatypes.length (estimated_trading_volume record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 9 (ask_level_1_price record) ++
      encode_bytes 9 (bid_level_1_price record) ++
      encode_bytes 9 (ask_level_1_volume record) ++
      encode_bytes 9 (bid_level_1_volume record) ++
      encode_bytes 5 (ask_level_1_order_counts record) ++
      encode_bytes 5 (bid_level_1_order_counts record) ++
      encode_bytes 9 (ask_level_2_price record) ++
      encode_bytes 9 (bid_level_2_price record) ++
      encode_bytes 9 (ask_level_2_volume record) ++
      encode_bytes 9 (bid_level_2_volume record) ++
      encode_bytes 5 (ask_level_2_order_counts record) ++
      encode_bytes 5 (bid_level_2_order_counts record) ++
      encode_bytes 9 (ask_level_3_price record) ++
      encode_bytes 9 (bid_level_3_price record) ++
      encode_bytes 9 (ask_level_3_volume record) ++
      encode_bytes 9 (bid_level_3_volume record) ++
      encode_bytes 5 (ask_level_3_order_counts record) ++
      encode_bytes 5 (bid_level_3_order_counts record) ++
      encode_bytes 9 (ask_level_4_price record) ++
      encode_bytes 9 (bid_level_4_price record) ++
      encode_bytes 9 (ask_level_4_volume record) ++
      encode_bytes 9 (bid_level_4_volume record) ++
      encode_bytes 5 (ask_level_4_order_counts record) ++
      encode_bytes 5 (bid_level_4_order_counts record) ++
      encode_bytes 9 (ask_level_5_price record) ++
      encode_bytes 9 (bid_level_5_price record) ++
      encode_bytes 9 (ask_level_5_volume record) ++
      encode_bytes 9 (bid_level_5_volume record) ++
      encode_bytes 5 (ask_level_5_order_counts record) ++
      encode_bytes 5 (bid_level_5_order_counts record) ++
      encode_bytes 9 (ask_total_volume record) ++
      encode_bytes 9 (bid_total_volume record) ++
      encode_bytes 5 (ask_price_valid_counts record) ++
      encode_bytes 5 (bid_price_valid_counts record) ++
      encode_bytes 9 (estimated_trading_price record) ++
      encode_bytes 9 (estimated_trading_volume record) ++
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
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (ask_level_1_price_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (bid_level_1_price_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (ask_level_1_volume_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (bid_level_1_volume_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (ask_level_1_order_counts_value, bytes) =>
                                                  match decode_bytes 5 bytes with
                                                  | None => None
                                                  | Some (bid_level_1_order_counts_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (ask_level_2_price_value, bytes) =>
                                                          match decode_bytes 9 bytes with
                                                          | None => None
                                                          | Some (bid_level_2_price_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (ask_level_2_volume_value, bytes) =>
                                                                  match decode_bytes 9 bytes with
                                                                  | None => None
                                                                  | Some (bid_level_2_volume_value, bytes) =>
                                                                      match decode_bytes 5 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_2_order_counts_value, bytes) =>
                                                                          match decode_bytes 5 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_2_order_counts_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_3_price_value, bytes) =>
                                                                                  match decode_bytes 9 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_3_price_value, bytes) =>
                                                                                      match decode_bytes 9 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_level_3_volume_value, bytes) =>
                                                                                          match decode_bytes 9 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_level_3_volume_value, bytes) =>
                                                                                              match decode_bytes 5 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_level_3_order_counts_value, bytes) =>
                                                                                                  match decode_bytes 5 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_level_3_order_counts_value, bytes) =>
                                                                                                      match decode_bytes 9 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_4_price_value, bytes) =>
                                                                                                          match decode_bytes 9 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_4_price_value, bytes) =>
                                                                                                              match decode_bytes 9 bytes with
                                                                                                              | None => None
                                                                                                              | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_level_4_order_counts_value, bytes) =>
                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_level_4_order_counts_value, bytes) =>
                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_level_5_order_counts_value, bytes) =>
                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_level_5_order_counts_value, bytes) =>
                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_total_volume_value, bytes) =>
                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_total_volume_value, bytes) =>
                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ask_price_valid_counts_value, bytes) =>
                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (bid_price_valid_counts_value, bytes) =>
                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                  Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_1_order_counts := ask_level_1_order_counts_value; bid_level_1_order_counts := bid_level_1_order_counts_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_2_order_counts := ask_level_2_order_counts_value; bid_level_2_order_counts := bid_level_2_order_counts_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_3_order_counts := ask_level_3_order_counts_value; bid_level_3_order_counts := bid_level_3_order_counts_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_4_order_counts := ask_level_4_order_counts_value; bid_level_4_order_counts := bid_level_4_order_counts_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_5_order_counts := ask_level_5_order_counts_value; bid_level_5_order_counts := bid_level_5_order_counts_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; ask_price_valid_counts := ask_price_valid_counts_value; bid_price_valid_counts := bid_price_valid_counts_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 319.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 bound_42]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_42.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativesQuoteFiveLevelsMessage.

  Module DerivativesQuoteTenLevelsMessage.

    (** Derivatives Quote (Ten levels). Multi-level bid/ask quotes with ten levels of depth. *)
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
      ask_level_1_order_counts : list byte;
      bid_level_1_order_counts : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_2_order_counts : list byte;
      bid_level_2_order_counts : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_3_order_counts : list byte;
      bid_level_3_order_counts : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_4_order_counts : list byte;
      bid_level_4_order_counts : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      ask_level_5_order_counts : list byte;
      bid_level_5_order_counts : list byte;
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      ask_level_6_order_counts : list byte;
      bid_level_6_order_counts : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      ask_level_7_order_counts : list byte;
      bid_level_7_order_counts : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      ask_level_8_order_counts : list byte;
      bid_level_8_order_counts : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      ask_level_9_order_counts : list byte;
      bid_level_9_order_counts : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      ask_level_10_order_counts : list byte;
      bid_level_10_order_counts : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      ask_price_valid_counts : list byte;
      bid_price_valid_counts : list byte;
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
      Datatypes.length (ask_level_1_price record) = 9 /\
      Datatypes.length (bid_level_1_price record) = 9 /\
      Datatypes.length (ask_level_1_volume record) = 9 /\
      Datatypes.length (bid_level_1_volume record) = 9 /\
      Datatypes.length (ask_level_1_order_counts record) = 5 /\
      Datatypes.length (bid_level_1_order_counts record) = 5 /\
      Datatypes.length (ask_level_2_price record) = 9 /\
      Datatypes.length (bid_level_2_price record) = 9 /\
      Datatypes.length (ask_level_2_volume record) = 9 /\
      Datatypes.length (bid_level_2_volume record) = 9 /\
      Datatypes.length (ask_level_2_order_counts record) = 5 /\
      Datatypes.length (bid_level_2_order_counts record) = 5 /\
      Datatypes.length (ask_level_3_price record) = 9 /\
      Datatypes.length (bid_level_3_price record) = 9 /\
      Datatypes.length (ask_level_3_volume record) = 9 /\
      Datatypes.length (bid_level_3_volume record) = 9 /\
      Datatypes.length (ask_level_3_order_counts record) = 5 /\
      Datatypes.length (bid_level_3_order_counts record) = 5 /\
      Datatypes.length (ask_level_4_price record) = 9 /\
      Datatypes.length (bid_level_4_price record) = 9 /\
      Datatypes.length (ask_level_4_volume record) = 9 /\
      Datatypes.length (bid_level_4_volume record) = 9 /\
      Datatypes.length (ask_level_4_order_counts record) = 5 /\
      Datatypes.length (bid_level_4_order_counts record) = 5 /\
      Datatypes.length (ask_level_5_price record) = 9 /\
      Datatypes.length (bid_level_5_price record) = 9 /\
      Datatypes.length (ask_level_5_volume record) = 9 /\
      Datatypes.length (bid_level_5_volume record) = 9 /\
      Datatypes.length (ask_level_5_order_counts record) = 5 /\
      Datatypes.length (bid_level_5_order_counts record) = 5 /\
      Datatypes.length (ask_level_6_price record) = 9 /\
      Datatypes.length (bid_level_6_price record) = 9 /\
      Datatypes.length (ask_level_6_volume record) = 9 /\
      Datatypes.length (bid_level_6_volume record) = 9 /\
      Datatypes.length (ask_level_6_order_counts record) = 5 /\
      Datatypes.length (bid_level_6_order_counts record) = 5 /\
      Datatypes.length (ask_level_7_price record) = 9 /\
      Datatypes.length (bid_level_7_price record) = 9 /\
      Datatypes.length (ask_level_7_volume record) = 9 /\
      Datatypes.length (bid_level_7_volume record) = 9 /\
      Datatypes.length (ask_level_7_order_counts record) = 5 /\
      Datatypes.length (bid_level_7_order_counts record) = 5 /\
      Datatypes.length (ask_level_8_price record) = 9 /\
      Datatypes.length (bid_level_8_price record) = 9 /\
      Datatypes.length (ask_level_8_volume record) = 9 /\
      Datatypes.length (bid_level_8_volume record) = 9 /\
      Datatypes.length (ask_level_8_order_counts record) = 5 /\
      Datatypes.length (bid_level_8_order_counts record) = 5 /\
      Datatypes.length (ask_level_9_price record) = 9 /\
      Datatypes.length (bid_level_9_price record) = 9 /\
      Datatypes.length (ask_level_9_volume record) = 9 /\
      Datatypes.length (bid_level_9_volume record) = 9 /\
      Datatypes.length (ask_level_9_order_counts record) = 5 /\
      Datatypes.length (bid_level_9_order_counts record) = 5 /\
      Datatypes.length (ask_level_10_price record) = 9 /\
      Datatypes.length (bid_level_10_price record) = 9 /\
      Datatypes.length (ask_level_10_volume record) = 9 /\
      Datatypes.length (bid_level_10_volume record) = 9 /\
      Datatypes.length (ask_level_10_order_counts record) = 5 /\
      Datatypes.length (bid_level_10_order_counts record) = 5 /\
      Datatypes.length (ask_total_volume record) = 9 /\
      Datatypes.length (bid_total_volume record) = 9 /\
      Datatypes.length (ask_price_valid_counts record) = 5 /\
      Datatypes.length (bid_price_valid_counts record) = 5 /\
      Datatypes.length (estimated_trading_price record) = 9 /\
      Datatypes.length (estimated_trading_volume record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 9 (ask_level_1_price record) ++
      encode_bytes 9 (bid_level_1_price record) ++
      encode_bytes 9 (ask_level_1_volume record) ++
      encode_bytes 9 (bid_level_1_volume record) ++
      encode_bytes 5 (ask_level_1_order_counts record) ++
      encode_bytes 5 (bid_level_1_order_counts record) ++
      encode_bytes 9 (ask_level_2_price record) ++
      encode_bytes 9 (bid_level_2_price record) ++
      encode_bytes 9 (ask_level_2_volume record) ++
      encode_bytes 9 (bid_level_2_volume record) ++
      encode_bytes 5 (ask_level_2_order_counts record) ++
      encode_bytes 5 (bid_level_2_order_counts record) ++
      encode_bytes 9 (ask_level_3_price record) ++
      encode_bytes 9 (bid_level_3_price record) ++
      encode_bytes 9 (ask_level_3_volume record) ++
      encode_bytes 9 (bid_level_3_volume record) ++
      encode_bytes 5 (ask_level_3_order_counts record) ++
      encode_bytes 5 (bid_level_3_order_counts record) ++
      encode_bytes 9 (ask_level_4_price record) ++
      encode_bytes 9 (bid_level_4_price record) ++
      encode_bytes 9 (ask_level_4_volume record) ++
      encode_bytes 9 (bid_level_4_volume record) ++
      encode_bytes 5 (ask_level_4_order_counts record) ++
      encode_bytes 5 (bid_level_4_order_counts record) ++
      encode_bytes 9 (ask_level_5_price record) ++
      encode_bytes 9 (bid_level_5_price record) ++
      encode_bytes 9 (ask_level_5_volume record) ++
      encode_bytes 9 (bid_level_5_volume record) ++
      encode_bytes 5 (ask_level_5_order_counts record) ++
      encode_bytes 5 (bid_level_5_order_counts record) ++
      encode_bytes 9 (ask_level_6_price record) ++
      encode_bytes 9 (bid_level_6_price record) ++
      encode_bytes 9 (ask_level_6_volume record) ++
      encode_bytes 9 (bid_level_6_volume record) ++
      encode_bytes 5 (ask_level_6_order_counts record) ++
      encode_bytes 5 (bid_level_6_order_counts record) ++
      encode_bytes 9 (ask_level_7_price record) ++
      encode_bytes 9 (bid_level_7_price record) ++
      encode_bytes 9 (ask_level_7_volume record) ++
      encode_bytes 9 (bid_level_7_volume record) ++
      encode_bytes 5 (ask_level_7_order_counts record) ++
      encode_bytes 5 (bid_level_7_order_counts record) ++
      encode_bytes 9 (ask_level_8_price record) ++
      encode_bytes 9 (bid_level_8_price record) ++
      encode_bytes 9 (ask_level_8_volume record) ++
      encode_bytes 9 (bid_level_8_volume record) ++
      encode_bytes 5 (ask_level_8_order_counts record) ++
      encode_bytes 5 (bid_level_8_order_counts record) ++
      encode_bytes 9 (ask_level_9_price record) ++
      encode_bytes 9 (bid_level_9_price record) ++
      encode_bytes 9 (ask_level_9_volume record) ++
      encode_bytes 9 (bid_level_9_volume record) ++
      encode_bytes 5 (ask_level_9_order_counts record) ++
      encode_bytes 5 (bid_level_9_order_counts record) ++
      encode_bytes 9 (ask_level_10_price record) ++
      encode_bytes 9 (bid_level_10_price record) ++
      encode_bytes 9 (ask_level_10_volume record) ++
      encode_bytes 9 (bid_level_10_volume record) ++
      encode_bytes 5 (ask_level_10_order_counts record) ++
      encode_bytes 5 (bid_level_10_order_counts record) ++
      encode_bytes 9 (ask_total_volume record) ++
      encode_bytes 9 (bid_total_volume record) ++
      encode_bytes 5 (ask_price_valid_counts record) ++
      encode_bytes 5 (bid_price_valid_counts record) ++
      encode_bytes 9 (estimated_trading_price record) ++
      encode_bytes 9 (estimated_trading_volume record) ++
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
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (ask_level_1_price_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (bid_level_1_price_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (ask_level_1_volume_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (bid_level_1_volume_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (ask_level_1_order_counts_value, bytes) =>
                                                  match decode_bytes 5 bytes with
                                                  | None => None
                                                  | Some (bid_level_1_order_counts_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (ask_level_2_price_value, bytes) =>
                                                          match decode_bytes 9 bytes with
                                                          | None => None
                                                          | Some (bid_level_2_price_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (ask_level_2_volume_value, bytes) =>
                                                                  match decode_bytes 9 bytes with
                                                                  | None => None
                                                                  | Some (bid_level_2_volume_value, bytes) =>
                                                                      match decode_bytes 5 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_2_order_counts_value, bytes) =>
                                                                          match decode_bytes 5 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_2_order_counts_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_3_price_value, bytes) =>
                                                                                  match decode_bytes 9 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_3_price_value, bytes) =>
                                                                                      match decode_bytes 9 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_level_3_volume_value, bytes) =>
                                                                                          match decode_bytes 9 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_level_3_volume_value, bytes) =>
                                                                                              match decode_bytes 5 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_level_3_order_counts_value, bytes) =>
                                                                                                  match decode_bytes 5 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_level_3_order_counts_value, bytes) =>
                                                                                                      match decode_bytes 9 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_4_price_value, bytes) =>
                                                                                                          match decode_bytes 9 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_4_price_value, bytes) =>
                                                                                                              match decode_bytes 9 bytes with
                                                                                                              | None => None
                                                                                                              | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_level_4_order_counts_value, bytes) =>
                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_level_4_order_counts_value, bytes) =>
                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_level_5_order_counts_value, bytes) =>
                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_level_5_order_counts_value, bytes) =>
                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_level_6_price_value, bytes) =>
                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_level_6_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ask_level_6_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (bid_level_6_volume_value, bytes) =>
                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_level_6_order_counts_value, bytes) =>
                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (bid_level_6_order_counts_value, bytes) =>
                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (ask_level_7_price_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (bid_level_7_price_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (ask_level_7_order_counts_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (bid_level_7_order_counts_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (ask_level_8_price_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (ask_level_8_order_counts_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (bid_level_8_order_counts_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (ask_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (ask_level_9_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (bid_level_9_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (ask_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (ask_level_10_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (bid_level_10_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (ask_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (bid_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (ask_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (bid_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_1_order_counts := ask_level_1_order_counts_value; bid_level_1_order_counts := bid_level_1_order_counts_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_2_order_counts := ask_level_2_order_counts_value; bid_level_2_order_counts := bid_level_2_order_counts_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_3_order_counts := ask_level_3_order_counts_value; bid_level_3_order_counts := bid_level_3_order_counts_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_4_order_counts := ask_level_4_order_counts_value; bid_level_4_order_counts := bid_level_4_order_counts_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_5_order_counts := ask_level_5_order_counts_value; bid_level_5_order_counts := bid_level_5_order_counts_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; ask_level_6_order_counts := ask_level_6_order_counts_value; bid_level_6_order_counts := bid_level_6_order_counts_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; ask_level_7_order_counts := ask_level_7_order_counts_value; bid_level_7_order_counts := bid_level_7_order_counts_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; ask_level_8_order_counts := ask_level_8_order_counts_value; bid_level_8_order_counts := bid_level_8_order_counts_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; ask_level_9_order_counts := ask_level_9_order_counts_value; bid_level_9_order_counts := bid_level_9_order_counts_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; ask_level_10_order_counts := ask_level_10_order_counts_value; bid_level_10_order_counts := bid_level_10_order_counts_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; ask_price_valid_counts := ask_price_valid_counts_value; bid_price_valid_counts := bid_price_valid_counts_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 549.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 bound_72]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_72.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativesQuoteTenLevelsMessage.

  Module DerivativesSnapshotFiveLevelsMessage.

    (** Derivatives Market Data Snapshot (Five Levels). Periodic full state snapshot with five levels of depth. *)
    Record t := {
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      trading_price : list byte;
      nearby_month_contract_trading_price : list byte;
      distant_month_contract_trading_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      open_interest : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_1_order_counts : list byte;
      bid_level_1_order_counts : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_2_order_counts : list byte;
      bid_level_2_order_counts : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_3_order_counts : list byte;
      bid_level_3_order_counts : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_4_order_counts : list byte;
      bid_level_4_order_counts : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      ask_level_5_order_counts : list byte;
      bid_level_5_order_counts : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      ask_price_valid_counts : list byte;
      bid_price_valid_counts : list byte;
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
      Datatypes.length (upper_limit_price record) = 9 /\
      Datatypes.length (lower_limit_price record) = 9 /\
      Datatypes.length (trading_price record) = 9 /\
      Datatypes.length (nearby_month_contract_trading_price record) = 9 /\
      Datatypes.length (distant_month_contract_trading_price record) = 9 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 9 /\
      Datatypes.length (todays_low record) = 9 /\
      Datatypes.length (open_interest record) = 10 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (ask_level_1_price record) = 9 /\
      Datatypes.length (bid_level_1_price record) = 9 /\
      Datatypes.length (ask_level_1_volume record) = 9 /\
      Datatypes.length (bid_level_1_volume record) = 9 /\
      Datatypes.length (ask_level_1_order_counts record) = 5 /\
      Datatypes.length (bid_level_1_order_counts record) = 5 /\
      Datatypes.length (ask_level_2_price record) = 9 /\
      Datatypes.length (bid_level_2_price record) = 9 /\
      Datatypes.length (ask_level_2_volume record) = 9 /\
      Datatypes.length (bid_level_2_volume record) = 9 /\
      Datatypes.length (ask_level_2_order_counts record) = 5 /\
      Datatypes.length (bid_level_2_order_counts record) = 5 /\
      Datatypes.length (ask_level_3_price record) = 9 /\
      Datatypes.length (bid_level_3_price record) = 9 /\
      Datatypes.length (ask_level_3_volume record) = 9 /\
      Datatypes.length (bid_level_3_volume record) = 9 /\
      Datatypes.length (ask_level_3_order_counts record) = 5 /\
      Datatypes.length (bid_level_3_order_counts record) = 5 /\
      Datatypes.length (ask_level_4_price record) = 9 /\
      Datatypes.length (bid_level_4_price record) = 9 /\
      Datatypes.length (ask_level_4_volume record) = 9 /\
      Datatypes.length (bid_level_4_volume record) = 9 /\
      Datatypes.length (ask_level_4_order_counts record) = 5 /\
      Datatypes.length (bid_level_4_order_counts record) = 5 /\
      Datatypes.length (ask_level_5_price record) = 9 /\
      Datatypes.length (bid_level_5_price record) = 9 /\
      Datatypes.length (ask_level_5_volume record) = 9 /\
      Datatypes.length (bid_level_5_volume record) = 9 /\
      Datatypes.length (ask_level_5_order_counts record) = 5 /\
      Datatypes.length (bid_level_5_order_counts record) = 5 /\
      Datatypes.length (ask_total_volume record) = 9 /\
      Datatypes.length (bid_total_volume record) = 9 /\
      Datatypes.length (ask_price_valid_counts record) = 5 /\
      Datatypes.length (bid_price_valid_counts record) = 5 /\
      Datatypes.length (estimated_trading_price record) = 9 /\
      Datatypes.length (estimated_trading_volume record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 9 (upper_limit_price record) ++
      encode_bytes 9 (lower_limit_price record) ++
      encode_bytes 9 (trading_price record) ++
      encode_bytes 9 (nearby_month_contract_trading_price record) ++
      encode_bytes 9 (distant_month_contract_trading_price record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 9 (todays_high record) ++
      encode_bytes 9 (todays_low record) ++
      encode_bytes 10 (open_interest record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 9 (ask_level_1_price record) ++
      encode_bytes 9 (bid_level_1_price record) ++
      encode_bytes 9 (ask_level_1_volume record) ++
      encode_bytes 9 (bid_level_1_volume record) ++
      encode_bytes 5 (ask_level_1_order_counts record) ++
      encode_bytes 5 (bid_level_1_order_counts record) ++
      encode_bytes 9 (ask_level_2_price record) ++
      encode_bytes 9 (bid_level_2_price record) ++
      encode_bytes 9 (ask_level_2_volume record) ++
      encode_bytes 9 (bid_level_2_volume record) ++
      encode_bytes 5 (ask_level_2_order_counts record) ++
      encode_bytes 5 (bid_level_2_order_counts record) ++
      encode_bytes 9 (ask_level_3_price record) ++
      encode_bytes 9 (bid_level_3_price record) ++
      encode_bytes 9 (ask_level_3_volume record) ++
      encode_bytes 9 (bid_level_3_volume record) ++
      encode_bytes 5 (ask_level_3_order_counts record) ++
      encode_bytes 5 (bid_level_3_order_counts record) ++
      encode_bytes 9 (ask_level_4_price record) ++
      encode_bytes 9 (bid_level_4_price record) ++
      encode_bytes 9 (ask_level_4_volume record) ++
      encode_bytes 9 (bid_level_4_volume record) ++
      encode_bytes 5 (ask_level_4_order_counts record) ++
      encode_bytes 5 (bid_level_4_order_counts record) ++
      encode_bytes 9 (ask_level_5_price record) ++
      encode_bytes 9 (bid_level_5_price record) ++
      encode_bytes 9 (ask_level_5_volume record) ++
      encode_bytes 9 (bid_level_5_volume record) ++
      encode_bytes 5 (ask_level_5_order_counts record) ++
      encode_bytes 5 (bid_level_5_order_counts record) ++
      encode_bytes 9 (ask_total_volume record) ++
      encode_bytes 9 (bid_total_volume record) ++
      encode_bytes 5 (ask_price_valid_counts record) ++
      encode_bytes 5 (bid_price_valid_counts record) ++
      encode_bytes 9 (estimated_trading_price record) ++
      encode_bytes 9 (estimated_trading_volume record) ++
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
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (upper_limit_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (lower_limit_price_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (nearby_month_contract_trading_price_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (distant_month_contract_trading_price_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (opening_price_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (todays_high_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (todays_low_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (open_interest_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_volume_value, bytes) =>
                                                              match decode_bytes 22 bytes with
                                                              | None => None
                                                              | Some (accumulated_trading_value_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (final_ask_bid_type_code_value, bytes) =>
                                                                      match decode_bytes 9 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_1_price_value, bytes) =>
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_1_price_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_1_volume_value, bytes) =>
                                                                                  match decode_bytes 9 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_1_volume_value, bytes) =>
                                                                                      match decode_bytes 5 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_level_1_order_counts_value, bytes) =>
                                                                                          match decode_bytes 5 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_level_1_order_counts_value, bytes) =>
                                                                                              match decode_bytes 9 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_level_2_price_value, bytes) =>
                                                                                                  match decode_bytes 9 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_level_2_price_value, bytes) =>
                                                                                                      match decode_bytes 9 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_2_volume_value, bytes) =>
                                                                                                          match decode_bytes 9 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_2_volume_value, bytes) =>
                                                                                                              match decode_bytes 5 bytes with
                                                                                                              | None => None
                                                                                                              | Some (ask_level_2_order_counts_value, bytes) =>
                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (bid_level_2_order_counts_value, bytes) =>
                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_level_3_price_value, bytes) =>
                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_level_3_price_value, bytes) =>
                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (ask_level_3_volume_value, bytes) =>
                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_level_3_order_counts_value, bytes) =>
                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (bid_level_3_order_counts_value, bytes) =>
                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ask_level_4_order_counts_value, bytes) =>
                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (bid_level_4_order_counts_value, bytes) =>
                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (ask_level_5_order_counts_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (bid_level_5_order_counts_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (ask_total_volume_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (bid_total_volume_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (ask_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (bid_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                          Some ({| board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; trading_price := trading_price_value; nearby_month_contract_trading_price := nearby_month_contract_trading_price_value; distant_month_contract_trading_price := distant_month_contract_trading_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; open_interest := open_interest_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_1_order_counts := ask_level_1_order_counts_value; bid_level_1_order_counts := bid_level_1_order_counts_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_2_order_counts := ask_level_2_order_counts_value; bid_level_2_order_counts := bid_level_2_order_counts_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_3_order_counts := ask_level_3_order_counts_value; bid_level_3_order_counts := bid_level_3_order_counts_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_4_order_counts := ask_level_4_order_counts_value; bid_level_4_order_counts := bid_level_4_order_counts_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_5_order_counts := ask_level_5_order_counts_value; bid_level_5_order_counts := bid_level_5_order_counts_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; ask_price_valid_counts := ask_price_valid_counts_value; bid_price_valid_counts := bid_price_valid_counts_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 416.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 bound_52]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_52.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativesSnapshotFiveLevelsMessage.

  Module DerivativesSnapshotTenLevelsMessage.

    (** Derivatives Market Data Snapshot (Ten Levels). Periodic full state snapshot with ten levels of depth. *)
    Record t := {
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      trading_price : list byte;
      nearby_month_contract_trading_price : list byte;
      distant_month_contract_trading_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      open_interest : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_1_order_counts : list byte;
      bid_level_1_order_counts : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_2_order_counts : list byte;
      bid_level_2_order_counts : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_3_order_counts : list byte;
      bid_level_3_order_counts : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_4_order_counts : list byte;
      bid_level_4_order_counts : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      ask_level_5_order_counts : list byte;
      bid_level_5_order_counts : list byte;
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      ask_level_6_order_counts : list byte;
      bid_level_6_order_counts : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      ask_level_7_order_counts : list byte;
      bid_level_7_order_counts : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      ask_level_8_order_counts : list byte;
      bid_level_8_order_counts : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      ask_level_9_order_counts : list byte;
      bid_level_9_order_counts : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      ask_level_10_order_counts : list byte;
      bid_level_10_order_counts : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      ask_price_valid_counts : list byte;
      bid_price_valid_counts : list byte;
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
      Datatypes.length (upper_limit_price record) = 9 /\
      Datatypes.length (lower_limit_price record) = 9 /\
      Datatypes.length (trading_price record) = 9 /\
      Datatypes.length (nearby_month_contract_trading_price record) = 9 /\
      Datatypes.length (distant_month_contract_trading_price record) = 9 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 9 /\
      Datatypes.length (todays_low record) = 9 /\
      Datatypes.length (open_interest record) = 10 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (ask_level_1_price record) = 9 /\
      Datatypes.length (bid_level_1_price record) = 9 /\
      Datatypes.length (ask_level_1_volume record) = 9 /\
      Datatypes.length (bid_level_1_volume record) = 9 /\
      Datatypes.length (ask_level_1_order_counts record) = 5 /\
      Datatypes.length (bid_level_1_order_counts record) = 5 /\
      Datatypes.length (ask_level_2_price record) = 9 /\
      Datatypes.length (bid_level_2_price record) = 9 /\
      Datatypes.length (ask_level_2_volume record) = 9 /\
      Datatypes.length (bid_level_2_volume record) = 9 /\
      Datatypes.length (ask_level_2_order_counts record) = 5 /\
      Datatypes.length (bid_level_2_order_counts record) = 5 /\
      Datatypes.length (ask_level_3_price record) = 9 /\
      Datatypes.length (bid_level_3_price record) = 9 /\
      Datatypes.length (ask_level_3_volume record) = 9 /\
      Datatypes.length (bid_level_3_volume record) = 9 /\
      Datatypes.length (ask_level_3_order_counts record) = 5 /\
      Datatypes.length (bid_level_3_order_counts record) = 5 /\
      Datatypes.length (ask_level_4_price record) = 9 /\
      Datatypes.length (bid_level_4_price record) = 9 /\
      Datatypes.length (ask_level_4_volume record) = 9 /\
      Datatypes.length (bid_level_4_volume record) = 9 /\
      Datatypes.length (ask_level_4_order_counts record) = 5 /\
      Datatypes.length (bid_level_4_order_counts record) = 5 /\
      Datatypes.length (ask_level_5_price record) = 9 /\
      Datatypes.length (bid_level_5_price record) = 9 /\
      Datatypes.length (ask_level_5_volume record) = 9 /\
      Datatypes.length (bid_level_5_volume record) = 9 /\
      Datatypes.length (ask_level_5_order_counts record) = 5 /\
      Datatypes.length (bid_level_5_order_counts record) = 5 /\
      Datatypes.length (ask_level_6_price record) = 9 /\
      Datatypes.length (bid_level_6_price record) = 9 /\
      Datatypes.length (ask_level_6_volume record) = 9 /\
      Datatypes.length (bid_level_6_volume record) = 9 /\
      Datatypes.length (ask_level_6_order_counts record) = 5 /\
      Datatypes.length (bid_level_6_order_counts record) = 5 /\
      Datatypes.length (ask_level_7_price record) = 9 /\
      Datatypes.length (bid_level_7_price record) = 9 /\
      Datatypes.length (ask_level_7_volume record) = 9 /\
      Datatypes.length (bid_level_7_volume record) = 9 /\
      Datatypes.length (ask_level_7_order_counts record) = 5 /\
      Datatypes.length (bid_level_7_order_counts record) = 5 /\
      Datatypes.length (ask_level_8_price record) = 9 /\
      Datatypes.length (bid_level_8_price record) = 9 /\
      Datatypes.length (ask_level_8_volume record) = 9 /\
      Datatypes.length (bid_level_8_volume record) = 9 /\
      Datatypes.length (ask_level_8_order_counts record) = 5 /\
      Datatypes.length (bid_level_8_order_counts record) = 5 /\
      Datatypes.length (ask_level_9_price record) = 9 /\
      Datatypes.length (bid_level_9_price record) = 9 /\
      Datatypes.length (ask_level_9_volume record) = 9 /\
      Datatypes.length (bid_level_9_volume record) = 9 /\
      Datatypes.length (ask_level_9_order_counts record) = 5 /\
      Datatypes.length (bid_level_9_order_counts record) = 5 /\
      Datatypes.length (ask_level_10_price record) = 9 /\
      Datatypes.length (bid_level_10_price record) = 9 /\
      Datatypes.length (ask_level_10_volume record) = 9 /\
      Datatypes.length (bid_level_10_volume record) = 9 /\
      Datatypes.length (ask_level_10_order_counts record) = 5 /\
      Datatypes.length (bid_level_10_order_counts record) = 5 /\
      Datatypes.length (ask_total_volume record) = 9 /\
      Datatypes.length (bid_total_volume record) = 9 /\
      Datatypes.length (ask_price_valid_counts record) = 5 /\
      Datatypes.length (bid_price_valid_counts record) = 5 /\
      Datatypes.length (estimated_trading_price record) = 9 /\
      Datatypes.length (estimated_trading_volume record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 9 (upper_limit_price record) ++
      encode_bytes 9 (lower_limit_price record) ++
      encode_bytes 9 (trading_price record) ++
      encode_bytes 9 (nearby_month_contract_trading_price record) ++
      encode_bytes 9 (distant_month_contract_trading_price record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 9 (todays_high record) ++
      encode_bytes 9 (todays_low record) ++
      encode_bytes 10 (open_interest record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 9 (ask_level_1_price record) ++
      encode_bytes 9 (bid_level_1_price record) ++
      encode_bytes 9 (ask_level_1_volume record) ++
      encode_bytes 9 (bid_level_1_volume record) ++
      encode_bytes 5 (ask_level_1_order_counts record) ++
      encode_bytes 5 (bid_level_1_order_counts record) ++
      encode_bytes 9 (ask_level_2_price record) ++
      encode_bytes 9 (bid_level_2_price record) ++
      encode_bytes 9 (ask_level_2_volume record) ++
      encode_bytes 9 (bid_level_2_volume record) ++
      encode_bytes 5 (ask_level_2_order_counts record) ++
      encode_bytes 5 (bid_level_2_order_counts record) ++
      encode_bytes 9 (ask_level_3_price record) ++
      encode_bytes 9 (bid_level_3_price record) ++
      encode_bytes 9 (ask_level_3_volume record) ++
      encode_bytes 9 (bid_level_3_volume record) ++
      encode_bytes 5 (ask_level_3_order_counts record) ++
      encode_bytes 5 (bid_level_3_order_counts record) ++
      encode_bytes 9 (ask_level_4_price record) ++
      encode_bytes 9 (bid_level_4_price record) ++
      encode_bytes 9 (ask_level_4_volume record) ++
      encode_bytes 9 (bid_level_4_volume record) ++
      encode_bytes 5 (ask_level_4_order_counts record) ++
      encode_bytes 5 (bid_level_4_order_counts record) ++
      encode_bytes 9 (ask_level_5_price record) ++
      encode_bytes 9 (bid_level_5_price record) ++
      encode_bytes 9 (ask_level_5_volume record) ++
      encode_bytes 9 (bid_level_5_volume record) ++
      encode_bytes 5 (ask_level_5_order_counts record) ++
      encode_bytes 5 (bid_level_5_order_counts record) ++
      encode_bytes 9 (ask_level_6_price record) ++
      encode_bytes 9 (bid_level_6_price record) ++
      encode_bytes 9 (ask_level_6_volume record) ++
      encode_bytes 9 (bid_level_6_volume record) ++
      encode_bytes 5 (ask_level_6_order_counts record) ++
      encode_bytes 5 (bid_level_6_order_counts record) ++
      encode_bytes 9 (ask_level_7_price record) ++
      encode_bytes 9 (bid_level_7_price record) ++
      encode_bytes 9 (ask_level_7_volume record) ++
      encode_bytes 9 (bid_level_7_volume record) ++
      encode_bytes 5 (ask_level_7_order_counts record) ++
      encode_bytes 5 (bid_level_7_order_counts record) ++
      encode_bytes 9 (ask_level_8_price record) ++
      encode_bytes 9 (bid_level_8_price record) ++
      encode_bytes 9 (ask_level_8_volume record) ++
      encode_bytes 9 (bid_level_8_volume record) ++
      encode_bytes 5 (ask_level_8_order_counts record) ++
      encode_bytes 5 (bid_level_8_order_counts record) ++
      encode_bytes 9 (ask_level_9_price record) ++
      encode_bytes 9 (bid_level_9_price record) ++
      encode_bytes 9 (ask_level_9_volume record) ++
      encode_bytes 9 (bid_level_9_volume record) ++
      encode_bytes 5 (ask_level_9_order_counts record) ++
      encode_bytes 5 (bid_level_9_order_counts record) ++
      encode_bytes 9 (ask_level_10_price record) ++
      encode_bytes 9 (bid_level_10_price record) ++
      encode_bytes 9 (ask_level_10_volume record) ++
      encode_bytes 9 (bid_level_10_volume record) ++
      encode_bytes 5 (ask_level_10_order_counts record) ++
      encode_bytes 5 (bid_level_10_order_counts record) ++
      encode_bytes 9 (ask_total_volume record) ++
      encode_bytes 9 (bid_total_volume record) ++
      encode_bytes 5 (ask_price_valid_counts record) ++
      encode_bytes 5 (bid_price_valid_counts record) ++
      encode_bytes 9 (estimated_trading_price record) ++
      encode_bytes 9 (estimated_trading_volume record) ++
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
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (upper_limit_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (lower_limit_price_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (nearby_month_contract_trading_price_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (distant_month_contract_trading_price_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (opening_price_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (todays_high_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (todays_low_value, bytes) =>
                                                      match decode_bytes 10 bytes with
                                                      | None => None
                                                      | Some (open_interest_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (accumulated_trading_volume_value, bytes) =>
                                                              match decode_bytes 22 bytes with
                                                              | None => None
                                                              | Some (accumulated_trading_value_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (final_ask_bid_type_code_value, bytes) =>
                                                                      match decode_bytes 9 bytes with
                                                                      | None => None
                                                                      | Some (ask_level_1_price_value, bytes) =>
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (bid_level_1_price_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (ask_level_1_volume_value, bytes) =>
                                                                                  match decode_bytes 9 bytes with
                                                                                  | None => None
                                                                                  | Some (bid_level_1_volume_value, bytes) =>
                                                                                      match decode_bytes 5 bytes with
                                                                                      | None => None
                                                                                      | Some (ask_level_1_order_counts_value, bytes) =>
                                                                                          match decode_bytes 5 bytes with
                                                                                          | None => None
                                                                                          | Some (bid_level_1_order_counts_value, bytes) =>
                                                                                              match decode_bytes 9 bytes with
                                                                                              | None => None
                                                                                              | Some (ask_level_2_price_value, bytes) =>
                                                                                                  match decode_bytes 9 bytes with
                                                                                                  | None => None
                                                                                                  | Some (bid_level_2_price_value, bytes) =>
                                                                                                      match decode_bytes 9 bytes with
                                                                                                      | None => None
                                                                                                      | Some (ask_level_2_volume_value, bytes) =>
                                                                                                          match decode_bytes 9 bytes with
                                                                                                          | None => None
                                                                                                          | Some (bid_level_2_volume_value, bytes) =>
                                                                                                              match decode_bytes 5 bytes with
                                                                                                              | None => None
                                                                                                              | Some (ask_level_2_order_counts_value, bytes) =>
                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (bid_level_2_order_counts_value, bytes) =>
                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (ask_level_3_price_value, bytes) =>
                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (bid_level_3_price_value, bytes) =>
                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (ask_level_3_volume_value, bytes) =>
                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (ask_level_3_order_counts_value, bytes) =>
                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (bid_level_3_order_counts_value, bytes) =>
                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (ask_level_4_order_counts_value, bytes) =>
                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (bid_level_4_order_counts_value, bytes) =>
                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (ask_level_5_order_counts_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (bid_level_5_order_counts_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (ask_level_6_price_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (bid_level_6_price_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (ask_level_6_order_counts_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (bid_level_6_order_counts_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (ask_level_7_price_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (bid_level_7_price_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (ask_level_7_order_counts_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (bid_level_7_order_counts_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (ask_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (ask_level_8_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (bid_level_8_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (ask_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (ask_level_9_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (bid_level_9_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (ask_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (ask_level_10_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (bid_level_10_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (ask_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (bid_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (ask_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (bid_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  Some ({| board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; trading_price := trading_price_value; nearby_month_contract_trading_price := nearby_month_contract_trading_price_value; distant_month_contract_trading_price := distant_month_contract_trading_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; open_interest := open_interest_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_1_order_counts := ask_level_1_order_counts_value; bid_level_1_order_counts := bid_level_1_order_counts_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_2_order_counts := ask_level_2_order_counts_value; bid_level_2_order_counts := bid_level_2_order_counts_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_3_order_counts := ask_level_3_order_counts_value; bid_level_3_order_counts := bid_level_3_order_counts_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_4_order_counts := ask_level_4_order_counts_value; bid_level_4_order_counts := bid_level_4_order_counts_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_5_order_counts := ask_level_5_order_counts_value; bid_level_5_order_counts := bid_level_5_order_counts_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; ask_level_6_order_counts := ask_level_6_order_counts_value; bid_level_6_order_counts := bid_level_6_order_counts_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; ask_level_7_order_counts := ask_level_7_order_counts_value; bid_level_7_order_counts := bid_level_7_order_counts_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; ask_level_8_order_counts := ask_level_8_order_counts_value; bid_level_8_order_counts := bid_level_8_order_counts_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; ask_level_9_order_counts := ask_level_9_order_counts_value; bid_level_9_order_counts := bid_level_9_order_counts_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; ask_level_10_order_counts := ask_level_10_order_counts_value; bid_level_10_order_counts := bid_level_10_order_counts_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; ask_price_valid_counts := ask_price_valid_counts_value; bid_price_valid_counts := bid_price_valid_counts_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 646.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 bound_82]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_82.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativesSnapshotTenLevelsMessage.

  Module DerivativesOrderFilledMessage.

    (** Derivatives Order Filled. Real-time trade prints with running totals for futures and options. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      nearby_month_contract_trading_price : list byte;
      distant_month_contract_trading_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      previous_price : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      upper_limit_of_dynamic_price_range : list byte;
      lower_limit_of_dynamic_price_range : list byte;
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
      Datatypes.length (trading_price record) = 9 /\
      Datatypes.length (trading_volume record) = 9 /\
      Datatypes.length (nearby_month_contract_trading_price record) = 9 /\
      Datatypes.length (distant_month_contract_trading_price record) = 9 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 9 /\
      Datatypes.length (todays_low record) = 9 /\
      Datatypes.length (previous_price record) = 9 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (upper_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (lower_limit_of_dynamic_price_range record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 9 (trading_price record) ++
      encode_bytes 9 (trading_volume record) ++
      encode_bytes 9 (nearby_month_contract_trading_price record) ++
      encode_bytes 9 (distant_month_contract_trading_price record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 9 (todays_high record) ++
      encode_bytes 9 (todays_low record) ++
      encode_bytes 9 (previous_price record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 9 (upper_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (lower_limit_of_dynamic_price_range record) ++
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
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (trading_volume_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (nearby_month_contract_trading_price_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (distant_month_contract_trading_price_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (opening_price_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (todays_high_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (todays_low_value, bytes) =>
                                                          match decode_bytes 9 bytes with
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
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (upper_limit_of_dynamic_price_range_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (lower_limit_of_dynamic_price_range_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; nearby_month_contract_trading_price := nearby_month_contract_trading_price_value; distant_month_contract_trading_price := distant_month_contract_trading_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; previous_price := previous_price_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; upper_limit_of_dynamic_price_range := upper_limit_of_dynamic_price_range_value; lower_limit_of_dynamic_price_range := lower_limit_of_dynamic_price_range_value; end_keyword := end_keyword_value |}, bytes)
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 168.
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

  End DerivativesOrderFilledMessage.

  Module DerivativesOrderFilledPlusQuoteFiveLevelsMessage.

    (** Derivatives Order Filled plus Quote (Five levels). Trade print followed by full five-level quote state. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      nearby_month_contract_trading_price : list byte;
      distant_month_contract_trading_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      previous_price : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      upper_limit_of_dynamic_price_range : list byte;
      lower_limit_of_dynamic_price_range : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_1_order_counts : list byte;
      bid_level_1_order_counts : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_2_order_counts : list byte;
      bid_level_2_order_counts : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_3_order_counts : list byte;
      bid_level_3_order_counts : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_4_order_counts : list byte;
      bid_level_4_order_counts : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      ask_level_5_order_counts : list byte;
      bid_level_5_order_counts : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      ask_price_valid_counts : list byte;
      bid_price_valid_counts : list byte;
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
      Datatypes.length (trading_price record) = 9 /\
      Datatypes.length (trading_volume record) = 9 /\
      Datatypes.length (nearby_month_contract_trading_price record) = 9 /\
      Datatypes.length (distant_month_contract_trading_price record) = 9 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 9 /\
      Datatypes.length (todays_low record) = 9 /\
      Datatypes.length (previous_price record) = 9 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (upper_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (lower_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (ask_level_1_price record) = 9 /\
      Datatypes.length (bid_level_1_price record) = 9 /\
      Datatypes.length (ask_level_1_volume record) = 9 /\
      Datatypes.length (bid_level_1_volume record) = 9 /\
      Datatypes.length (ask_level_1_order_counts record) = 5 /\
      Datatypes.length (bid_level_1_order_counts record) = 5 /\
      Datatypes.length (ask_level_2_price record) = 9 /\
      Datatypes.length (bid_level_2_price record) = 9 /\
      Datatypes.length (ask_level_2_volume record) = 9 /\
      Datatypes.length (bid_level_2_volume record) = 9 /\
      Datatypes.length (ask_level_2_order_counts record) = 5 /\
      Datatypes.length (bid_level_2_order_counts record) = 5 /\
      Datatypes.length (ask_level_3_price record) = 9 /\
      Datatypes.length (bid_level_3_price record) = 9 /\
      Datatypes.length (ask_level_3_volume record) = 9 /\
      Datatypes.length (bid_level_3_volume record) = 9 /\
      Datatypes.length (ask_level_3_order_counts record) = 5 /\
      Datatypes.length (bid_level_3_order_counts record) = 5 /\
      Datatypes.length (ask_level_4_price record) = 9 /\
      Datatypes.length (bid_level_4_price record) = 9 /\
      Datatypes.length (ask_level_4_volume record) = 9 /\
      Datatypes.length (bid_level_4_volume record) = 9 /\
      Datatypes.length (ask_level_4_order_counts record) = 5 /\
      Datatypes.length (bid_level_4_order_counts record) = 5 /\
      Datatypes.length (ask_level_5_price record) = 9 /\
      Datatypes.length (bid_level_5_price record) = 9 /\
      Datatypes.length (ask_level_5_volume record) = 9 /\
      Datatypes.length (bid_level_5_volume record) = 9 /\
      Datatypes.length (ask_level_5_order_counts record) = 5 /\
      Datatypes.length (bid_level_5_order_counts record) = 5 /\
      Datatypes.length (ask_total_volume record) = 9 /\
      Datatypes.length (bid_total_volume record) = 9 /\
      Datatypes.length (ask_price_valid_counts record) = 5 /\
      Datatypes.length (bid_price_valid_counts record) = 5 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 9 (trading_price record) ++
      encode_bytes 9 (trading_volume record) ++
      encode_bytes 9 (nearby_month_contract_trading_price record) ++
      encode_bytes 9 (distant_month_contract_trading_price record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 9 (todays_high record) ++
      encode_bytes 9 (todays_low record) ++
      encode_bytes 9 (previous_price record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 9 (upper_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (lower_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (ask_level_1_price record) ++
      encode_bytes 9 (bid_level_1_price record) ++
      encode_bytes 9 (ask_level_1_volume record) ++
      encode_bytes 9 (bid_level_1_volume record) ++
      encode_bytes 5 (ask_level_1_order_counts record) ++
      encode_bytes 5 (bid_level_1_order_counts record) ++
      encode_bytes 9 (ask_level_2_price record) ++
      encode_bytes 9 (bid_level_2_price record) ++
      encode_bytes 9 (ask_level_2_volume record) ++
      encode_bytes 9 (bid_level_2_volume record) ++
      encode_bytes 5 (ask_level_2_order_counts record) ++
      encode_bytes 5 (bid_level_2_order_counts record) ++
      encode_bytes 9 (ask_level_3_price record) ++
      encode_bytes 9 (bid_level_3_price record) ++
      encode_bytes 9 (ask_level_3_volume record) ++
      encode_bytes 9 (bid_level_3_volume record) ++
      encode_bytes 5 (ask_level_3_order_counts record) ++
      encode_bytes 5 (bid_level_3_order_counts record) ++
      encode_bytes 9 (ask_level_4_price record) ++
      encode_bytes 9 (bid_level_4_price record) ++
      encode_bytes 9 (ask_level_4_volume record) ++
      encode_bytes 9 (bid_level_4_volume record) ++
      encode_bytes 5 (ask_level_4_order_counts record) ++
      encode_bytes 5 (bid_level_4_order_counts record) ++
      encode_bytes 9 (ask_level_5_price record) ++
      encode_bytes 9 (bid_level_5_price record) ++
      encode_bytes 9 (ask_level_5_volume record) ++
      encode_bytes 9 (bid_level_5_volume record) ++
      encode_bytes 5 (ask_level_5_order_counts record) ++
      encode_bytes 5 (bid_level_5_order_counts record) ++
      encode_bytes 9 (ask_total_volume record) ++
      encode_bytes 9 (bid_total_volume record) ++
      encode_bytes 5 (ask_price_valid_counts record) ++
      encode_bytes 5 (bid_price_valid_counts record) ++
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
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (trading_volume_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (nearby_month_contract_trading_price_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (distant_month_contract_trading_price_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (opening_price_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (todays_high_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (todays_low_value, bytes) =>
                                                          match decode_bytes 9 bytes with
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
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (upper_limit_of_dynamic_price_range_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (lower_limit_of_dynamic_price_range_value, bytes) =>
                                                                                  match decode_bytes 9 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_1_price_value, bytes) =>
                                                                                      match decode_bytes 9 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_1_price_value, bytes) =>
                                                                                          match decode_bytes 9 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_1_volume_value, bytes) =>
                                                                                              match decode_bytes 9 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_1_volume_value, bytes) =>
                                                                                                  match decode_bytes 5 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_1_order_counts_value, bytes) =>
                                                                                                      match decode_bytes 5 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_1_order_counts_value, bytes) =>
                                                                                                          match decode_bytes 9 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                                                              match decode_bytes 9 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_2_volume_value, bytes) =>
                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_2_volume_value, bytes) =>
                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_2_order_counts_value, bytes) =>
                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_2_order_counts_value, bytes) =>
                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_3_price_value, bytes) =>
                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_3_price_value, bytes) =>
                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_3_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_level_3_order_counts_value, bytes) =>
                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_level_3_order_counts_value, bytes) =>
                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_level_4_order_counts_value, bytes) =>
                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (bid_level_4_order_counts_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (ask_level_5_order_counts_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (bid_level_5_order_counts_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_total_volume_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (bid_total_volume_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (ask_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bid_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; nearby_month_contract_trading_price := nearby_month_contract_trading_price_value; distant_month_contract_trading_price := distant_month_contract_trading_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; previous_price := previous_price_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; upper_limit_of_dynamic_price_range := upper_limit_of_dynamic_price_range_value; lower_limit_of_dynamic_price_range := lower_limit_of_dynamic_price_range_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_1_order_counts := ask_level_1_order_counts_value; bid_level_1_order_counts := bid_level_1_order_counts_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_2_order_counts := ask_level_2_order_counts_value; bid_level_2_order_counts := bid_level_2_order_counts_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_3_order_counts := ask_level_3_order_counts_value; bid_level_3_order_counts := bid_level_3_order_counts_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_4_order_counts := ask_level_4_order_counts_value; bid_level_4_order_counts := bid_level_4_order_counts_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_5_order_counts := ask_level_5_order_counts_value; bid_level_5_order_counts := bid_level_5_order_counts_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; ask_price_valid_counts := ask_price_valid_counts_value; bid_price_valid_counts := bid_price_valid_counts_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 426.
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

  End DerivativesOrderFilledPlusQuoteFiveLevelsMessage.

  Module DerivativesOrderFilledPlusQuoteTenLevelsMessage.

    (** Derivatives Order Filled plus Quote (Ten levels). Trade print followed by full ten-level quote state. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      trading_price : list byte;
      trading_volume : list byte;
      nearby_month_contract_trading_price : list byte;
      distant_month_contract_trading_price : list byte;
      opening_price : list byte;
      todays_high : list byte;
      todays_low : list byte;
      previous_price : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      final_ask_bid_type_code : list byte;
      upper_limit_of_dynamic_price_range : list byte;
      lower_limit_of_dynamic_price_range : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_1_order_counts : list byte;
      bid_level_1_order_counts : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_2_order_counts : list byte;
      bid_level_2_order_counts : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_3_order_counts : list byte;
      bid_level_3_order_counts : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_4_order_counts : list byte;
      bid_level_4_order_counts : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      ask_level_5_order_counts : list byte;
      bid_level_5_order_counts : list byte;
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      ask_level_6_order_counts : list byte;
      bid_level_6_order_counts : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      ask_level_7_order_counts : list byte;
      bid_level_7_order_counts : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      ask_level_8_order_counts : list byte;
      bid_level_8_order_counts : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      ask_level_9_order_counts : list byte;
      bid_level_9_order_counts : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      ask_level_10_order_counts : list byte;
      bid_level_10_order_counts : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      ask_price_valid_counts : list byte;
      bid_price_valid_counts : list byte;
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
      Datatypes.length (trading_price record) = 9 /\
      Datatypes.length (trading_volume record) = 9 /\
      Datatypes.length (nearby_month_contract_trading_price record) = 9 /\
      Datatypes.length (distant_month_contract_trading_price record) = 9 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (todays_high record) = 9 /\
      Datatypes.length (todays_low record) = 9 /\
      Datatypes.length (previous_price record) = 9 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (final_ask_bid_type_code record) = 1 /\
      Datatypes.length (upper_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (lower_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (ask_level_1_price record) = 9 /\
      Datatypes.length (bid_level_1_price record) = 9 /\
      Datatypes.length (ask_level_1_volume record) = 9 /\
      Datatypes.length (bid_level_1_volume record) = 9 /\
      Datatypes.length (ask_level_1_order_counts record) = 5 /\
      Datatypes.length (bid_level_1_order_counts record) = 5 /\
      Datatypes.length (ask_level_2_price record) = 9 /\
      Datatypes.length (bid_level_2_price record) = 9 /\
      Datatypes.length (ask_level_2_volume record) = 9 /\
      Datatypes.length (bid_level_2_volume record) = 9 /\
      Datatypes.length (ask_level_2_order_counts record) = 5 /\
      Datatypes.length (bid_level_2_order_counts record) = 5 /\
      Datatypes.length (ask_level_3_price record) = 9 /\
      Datatypes.length (bid_level_3_price record) = 9 /\
      Datatypes.length (ask_level_3_volume record) = 9 /\
      Datatypes.length (bid_level_3_volume record) = 9 /\
      Datatypes.length (ask_level_3_order_counts record) = 5 /\
      Datatypes.length (bid_level_3_order_counts record) = 5 /\
      Datatypes.length (ask_level_4_price record) = 9 /\
      Datatypes.length (bid_level_4_price record) = 9 /\
      Datatypes.length (ask_level_4_volume record) = 9 /\
      Datatypes.length (bid_level_4_volume record) = 9 /\
      Datatypes.length (ask_level_4_order_counts record) = 5 /\
      Datatypes.length (bid_level_4_order_counts record) = 5 /\
      Datatypes.length (ask_level_5_price record) = 9 /\
      Datatypes.length (bid_level_5_price record) = 9 /\
      Datatypes.length (ask_level_5_volume record) = 9 /\
      Datatypes.length (bid_level_5_volume record) = 9 /\
      Datatypes.length (ask_level_5_order_counts record) = 5 /\
      Datatypes.length (bid_level_5_order_counts record) = 5 /\
      Datatypes.length (ask_level_6_price record) = 9 /\
      Datatypes.length (bid_level_6_price record) = 9 /\
      Datatypes.length (ask_level_6_volume record) = 9 /\
      Datatypes.length (bid_level_6_volume record) = 9 /\
      Datatypes.length (ask_level_6_order_counts record) = 5 /\
      Datatypes.length (bid_level_6_order_counts record) = 5 /\
      Datatypes.length (ask_level_7_price record) = 9 /\
      Datatypes.length (bid_level_7_price record) = 9 /\
      Datatypes.length (ask_level_7_volume record) = 9 /\
      Datatypes.length (bid_level_7_volume record) = 9 /\
      Datatypes.length (ask_level_7_order_counts record) = 5 /\
      Datatypes.length (bid_level_7_order_counts record) = 5 /\
      Datatypes.length (ask_level_8_price record) = 9 /\
      Datatypes.length (bid_level_8_price record) = 9 /\
      Datatypes.length (ask_level_8_volume record) = 9 /\
      Datatypes.length (bid_level_8_volume record) = 9 /\
      Datatypes.length (ask_level_8_order_counts record) = 5 /\
      Datatypes.length (bid_level_8_order_counts record) = 5 /\
      Datatypes.length (ask_level_9_price record) = 9 /\
      Datatypes.length (bid_level_9_price record) = 9 /\
      Datatypes.length (ask_level_9_volume record) = 9 /\
      Datatypes.length (bid_level_9_volume record) = 9 /\
      Datatypes.length (ask_level_9_order_counts record) = 5 /\
      Datatypes.length (bid_level_9_order_counts record) = 5 /\
      Datatypes.length (ask_level_10_price record) = 9 /\
      Datatypes.length (bid_level_10_price record) = 9 /\
      Datatypes.length (ask_level_10_volume record) = 9 /\
      Datatypes.length (bid_level_10_volume record) = 9 /\
      Datatypes.length (ask_level_10_order_counts record) = 5 /\
      Datatypes.length (bid_level_10_order_counts record) = 5 /\
      Datatypes.length (ask_total_volume record) = 9 /\
      Datatypes.length (bid_total_volume record) = 9 /\
      Datatypes.length (ask_price_valid_counts record) = 5 /\
      Datatypes.length (bid_price_valid_counts record) = 5 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 9 (trading_price record) ++
      encode_bytes 9 (trading_volume record) ++
      encode_bytes 9 (nearby_month_contract_trading_price record) ++
      encode_bytes 9 (distant_month_contract_trading_price record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 9 (todays_high record) ++
      encode_bytes 9 (todays_low record) ++
      encode_bytes 9 (previous_price record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (final_ask_bid_type_code record) ++
      encode_bytes 9 (upper_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (lower_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (ask_level_1_price record) ++
      encode_bytes 9 (bid_level_1_price record) ++
      encode_bytes 9 (ask_level_1_volume record) ++
      encode_bytes 9 (bid_level_1_volume record) ++
      encode_bytes 5 (ask_level_1_order_counts record) ++
      encode_bytes 5 (bid_level_1_order_counts record) ++
      encode_bytes 9 (ask_level_2_price record) ++
      encode_bytes 9 (bid_level_2_price record) ++
      encode_bytes 9 (ask_level_2_volume record) ++
      encode_bytes 9 (bid_level_2_volume record) ++
      encode_bytes 5 (ask_level_2_order_counts record) ++
      encode_bytes 5 (bid_level_2_order_counts record) ++
      encode_bytes 9 (ask_level_3_price record) ++
      encode_bytes 9 (bid_level_3_price record) ++
      encode_bytes 9 (ask_level_3_volume record) ++
      encode_bytes 9 (bid_level_3_volume record) ++
      encode_bytes 5 (ask_level_3_order_counts record) ++
      encode_bytes 5 (bid_level_3_order_counts record) ++
      encode_bytes 9 (ask_level_4_price record) ++
      encode_bytes 9 (bid_level_4_price record) ++
      encode_bytes 9 (ask_level_4_volume record) ++
      encode_bytes 9 (bid_level_4_volume record) ++
      encode_bytes 5 (ask_level_4_order_counts record) ++
      encode_bytes 5 (bid_level_4_order_counts record) ++
      encode_bytes 9 (ask_level_5_price record) ++
      encode_bytes 9 (bid_level_5_price record) ++
      encode_bytes 9 (ask_level_5_volume record) ++
      encode_bytes 9 (bid_level_5_volume record) ++
      encode_bytes 5 (ask_level_5_order_counts record) ++
      encode_bytes 5 (bid_level_5_order_counts record) ++
      encode_bytes 9 (ask_level_6_price record) ++
      encode_bytes 9 (bid_level_6_price record) ++
      encode_bytes 9 (ask_level_6_volume record) ++
      encode_bytes 9 (bid_level_6_volume record) ++
      encode_bytes 5 (ask_level_6_order_counts record) ++
      encode_bytes 5 (bid_level_6_order_counts record) ++
      encode_bytes 9 (ask_level_7_price record) ++
      encode_bytes 9 (bid_level_7_price record) ++
      encode_bytes 9 (ask_level_7_volume record) ++
      encode_bytes 9 (bid_level_7_volume record) ++
      encode_bytes 5 (ask_level_7_order_counts record) ++
      encode_bytes 5 (bid_level_7_order_counts record) ++
      encode_bytes 9 (ask_level_8_price record) ++
      encode_bytes 9 (bid_level_8_price record) ++
      encode_bytes 9 (ask_level_8_volume record) ++
      encode_bytes 9 (bid_level_8_volume record) ++
      encode_bytes 5 (ask_level_8_order_counts record) ++
      encode_bytes 5 (bid_level_8_order_counts record) ++
      encode_bytes 9 (ask_level_9_price record) ++
      encode_bytes 9 (bid_level_9_price record) ++
      encode_bytes 9 (ask_level_9_volume record) ++
      encode_bytes 9 (bid_level_9_volume record) ++
      encode_bytes 5 (ask_level_9_order_counts record) ++
      encode_bytes 5 (bid_level_9_order_counts record) ++
      encode_bytes 9 (ask_level_10_price record) ++
      encode_bytes 9 (bid_level_10_price record) ++
      encode_bytes 9 (ask_level_10_volume record) ++
      encode_bytes 9 (bid_level_10_volume record) ++
      encode_bytes 5 (ask_level_10_order_counts record) ++
      encode_bytes 5 (bid_level_10_order_counts record) ++
      encode_bytes 9 (ask_total_volume record) ++
      encode_bytes 9 (bid_total_volume record) ++
      encode_bytes 5 (ask_price_valid_counts record) ++
      encode_bytes 5 (bid_price_valid_counts record) ++
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
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (trading_price_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (trading_volume_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (nearby_month_contract_trading_price_value, bytes) =>
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (distant_month_contract_trading_price_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (opening_price_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (todays_high_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (todays_low_value, bytes) =>
                                                          match decode_bytes 9 bytes with
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
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (upper_limit_of_dynamic_price_range_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (lower_limit_of_dynamic_price_range_value, bytes) =>
                                                                                  match decode_bytes 9 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_1_price_value, bytes) =>
                                                                                      match decode_bytes 9 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_1_price_value, bytes) =>
                                                                                          match decode_bytes 9 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_1_volume_value, bytes) =>
                                                                                              match decode_bytes 9 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_1_volume_value, bytes) =>
                                                                                                  match decode_bytes 5 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_1_order_counts_value, bytes) =>
                                                                                                      match decode_bytes 5 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_1_order_counts_value, bytes) =>
                                                                                                          match decode_bytes 9 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                                                              match decode_bytes 9 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_2_volume_value, bytes) =>
                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_2_volume_value, bytes) =>
                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_2_order_counts_value, bytes) =>
                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_2_order_counts_value, bytes) =>
                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_3_price_value, bytes) =>
                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_3_price_value, bytes) =>
                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_3_volume_value, bytes) =>
                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_level_3_order_counts_value, bytes) =>
                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_level_3_order_counts_value, bytes) =>
                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_level_4_order_counts_value, bytes) =>
                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (bid_level_4_order_counts_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (ask_level_5_order_counts_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (bid_level_5_order_counts_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_level_6_price_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (bid_level_6_price_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (ask_level_6_order_counts_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (bid_level_6_order_counts_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (ask_level_7_price_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (bid_level_7_price_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (ask_level_7_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (bid_level_7_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (ask_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (ask_level_8_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (bid_level_8_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (ask_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (ask_level_9_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (bid_level_9_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (ask_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (ask_level_10_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (bid_level_10_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (ask_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (bid_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (ask_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (bid_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; trading_price := trading_price_value; trading_volume := trading_volume_value; nearby_month_contract_trading_price := nearby_month_contract_trading_price_value; distant_month_contract_trading_price := distant_month_contract_trading_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; previous_price := previous_price_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; upper_limit_of_dynamic_price_range := upper_limit_of_dynamic_price_range_value; lower_limit_of_dynamic_price_range := lower_limit_of_dynamic_price_range_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_1_order_counts := ask_level_1_order_counts_value; bid_level_1_order_counts := bid_level_1_order_counts_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_2_order_counts := ask_level_2_order_counts_value; bid_level_2_order_counts := bid_level_2_order_counts_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_3_order_counts := ask_level_3_order_counts_value; bid_level_3_order_counts := bid_level_3_order_counts_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_4_order_counts := ask_level_4_order_counts_value; bid_level_4_order_counts := bid_level_4_order_counts_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_5_order_counts := ask_level_5_order_counts_value; bid_level_5_order_counts := bid_level_5_order_counts_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; ask_level_6_order_counts := ask_level_6_order_counts_value; bid_level_6_order_counts := bid_level_6_order_counts_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; ask_level_7_order_counts := ask_level_7_order_counts_value; bid_level_7_order_counts := bid_level_7_order_counts_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; ask_level_8_order_counts := ask_level_8_order_counts_value; bid_level_8_order_counts := bid_level_8_order_counts_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; ask_level_9_order_counts := ask_level_9_order_counts_value; bid_level_9_order_counts := bid_level_9_order_counts_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; ask_level_10_order_counts := ask_level_10_order_counts_value; bid_level_10_order_counts := bid_level_10_order_counts_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; ask_price_valid_counts := ask_price_valid_counts_value; bid_price_valid_counts := bid_price_valid_counts_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 656.
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

  End DerivativesOrderFilledPlusQuoteTenLevelsMessage.

  Module DerivativesMarketOperationTsPlusQuoteFiveLevelsMessage.

    (** Derivatives Market Operation TS plus Quote (Five levels). Per-issue session-state event followed by full five-level quote state. *)
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
      upper_limit_of_dynamic_price_range : list byte;
      lower_limit_of_dynamic_price_range : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_1_order_counts : list byte;
      bid_level_1_order_counts : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_2_order_counts : list byte;
      bid_level_2_order_counts : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_3_order_counts : list byte;
      bid_level_3_order_counts : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_4_order_counts : list byte;
      bid_level_4_order_counts : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      ask_level_5_order_counts : list byte;
      bid_level_5_order_counts : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      ask_price_valid_counts : list byte;
      bid_price_valid_counts : list byte;
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
      Datatypes.length (upper_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (lower_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (ask_level_1_price record) = 9 /\
      Datatypes.length (bid_level_1_price record) = 9 /\
      Datatypes.length (ask_level_1_volume record) = 9 /\
      Datatypes.length (bid_level_1_volume record) = 9 /\
      Datatypes.length (ask_level_1_order_counts record) = 5 /\
      Datatypes.length (bid_level_1_order_counts record) = 5 /\
      Datatypes.length (ask_level_2_price record) = 9 /\
      Datatypes.length (bid_level_2_price record) = 9 /\
      Datatypes.length (ask_level_2_volume record) = 9 /\
      Datatypes.length (bid_level_2_volume record) = 9 /\
      Datatypes.length (ask_level_2_order_counts record) = 5 /\
      Datatypes.length (bid_level_2_order_counts record) = 5 /\
      Datatypes.length (ask_level_3_price record) = 9 /\
      Datatypes.length (bid_level_3_price record) = 9 /\
      Datatypes.length (ask_level_3_volume record) = 9 /\
      Datatypes.length (bid_level_3_volume record) = 9 /\
      Datatypes.length (ask_level_3_order_counts record) = 5 /\
      Datatypes.length (bid_level_3_order_counts record) = 5 /\
      Datatypes.length (ask_level_4_price record) = 9 /\
      Datatypes.length (bid_level_4_price record) = 9 /\
      Datatypes.length (ask_level_4_volume record) = 9 /\
      Datatypes.length (bid_level_4_volume record) = 9 /\
      Datatypes.length (ask_level_4_order_counts record) = 5 /\
      Datatypes.length (bid_level_4_order_counts record) = 5 /\
      Datatypes.length (ask_level_5_price record) = 9 /\
      Datatypes.length (bid_level_5_price record) = 9 /\
      Datatypes.length (ask_level_5_volume record) = 9 /\
      Datatypes.length (bid_level_5_volume record) = 9 /\
      Datatypes.length (ask_level_5_order_counts record) = 5 /\
      Datatypes.length (bid_level_5_order_counts record) = 5 /\
      Datatypes.length (ask_total_volume record) = 9 /\
      Datatypes.length (bid_total_volume record) = 9 /\
      Datatypes.length (ask_price_valid_counts record) = 5 /\
      Datatypes.length (bid_price_valid_counts record) = 5 /\
      Datatypes.length (estimated_trading_price record) = 9 /\
      Datatypes.length (estimated_trading_volume record) = 9 /\
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
      encode_bytes 9 (upper_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (lower_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (ask_level_1_price record) ++
      encode_bytes 9 (bid_level_1_price record) ++
      encode_bytes 9 (ask_level_1_volume record) ++
      encode_bytes 9 (bid_level_1_volume record) ++
      encode_bytes 5 (ask_level_1_order_counts record) ++
      encode_bytes 5 (bid_level_1_order_counts record) ++
      encode_bytes 9 (ask_level_2_price record) ++
      encode_bytes 9 (bid_level_2_price record) ++
      encode_bytes 9 (ask_level_2_volume record) ++
      encode_bytes 9 (bid_level_2_volume record) ++
      encode_bytes 5 (ask_level_2_order_counts record) ++
      encode_bytes 5 (bid_level_2_order_counts record) ++
      encode_bytes 9 (ask_level_3_price record) ++
      encode_bytes 9 (bid_level_3_price record) ++
      encode_bytes 9 (ask_level_3_volume record) ++
      encode_bytes 9 (bid_level_3_volume record) ++
      encode_bytes 5 (ask_level_3_order_counts record) ++
      encode_bytes 5 (bid_level_3_order_counts record) ++
      encode_bytes 9 (ask_level_4_price record) ++
      encode_bytes 9 (bid_level_4_price record) ++
      encode_bytes 9 (ask_level_4_volume record) ++
      encode_bytes 9 (bid_level_4_volume record) ++
      encode_bytes 5 (ask_level_4_order_counts record) ++
      encode_bytes 5 (bid_level_4_order_counts record) ++
      encode_bytes 9 (ask_level_5_price record) ++
      encode_bytes 9 (bid_level_5_price record) ++
      encode_bytes 9 (ask_level_5_volume record) ++
      encode_bytes 9 (bid_level_5_volume record) ++
      encode_bytes 5 (ask_level_5_order_counts record) ++
      encode_bytes 5 (bid_level_5_order_counts record) ++
      encode_bytes 9 (ask_total_volume record) ++
      encode_bytes 9 (bid_total_volume record) ++
      encode_bytes 5 (ask_price_valid_counts record) ++
      encode_bytes 5 (bid_price_valid_counts record) ++
      encode_bytes 9 (estimated_trading_price record) ++
      encode_bytes 9 (estimated_trading_volume record) ++
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
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (upper_limit_of_dynamic_price_range_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (lower_limit_of_dynamic_price_range_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (ask_level_1_price_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (bid_level_1_price_value, bytes) =>
                                                          match decode_bytes 9 bytes with
                                                          | None => None
                                                          | Some (ask_level_1_volume_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (bid_level_1_volume_value, bytes) =>
                                                                  match decode_bytes 5 bytes with
                                                                  | None => None
                                                                  | Some (ask_level_1_order_counts_value, bytes) =>
                                                                      match decode_bytes 5 bytes with
                                                                      | None => None
                                                                      | Some (bid_level_1_order_counts_value, bytes) =>
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                  match decode_bytes 9 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_2_volume_value, bytes) =>
                                                                                      match decode_bytes 9 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_2_volume_value, bytes) =>
                                                                                          match decode_bytes 5 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_2_order_counts_value, bytes) =>
                                                                                              match decode_bytes 5 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_2_order_counts_value, bytes) =>
                                                                                                  match decode_bytes 9 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_3_price_value, bytes) =>
                                                                                                      match decode_bytes 9 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_3_price_value, bytes) =>
                                                                                                          match decode_bytes 9 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_3_volume_value, bytes) =>
                                                                                                              match decode_bytes 9 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_3_order_counts_value, bytes) =>
                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_3_order_counts_value, bytes) =>
                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_4_order_counts_value, bytes) =>
                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_4_order_counts_value, bytes) =>
                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_level_5_order_counts_value, bytes) =>
                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (bid_level_5_order_counts_value, bytes) =>
                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_total_volume_value, bytes) =>
                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (bid_total_volume_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (ask_price_valid_counts_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (bid_price_valid_counts_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; upper_limit_of_dynamic_price_range := upper_limit_of_dynamic_price_range_value; lower_limit_of_dynamic_price_range := lower_limit_of_dynamic_price_range_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_1_order_counts := ask_level_1_order_counts_value; bid_level_1_order_counts := bid_level_1_order_counts_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_2_order_counts := ask_level_2_order_counts_value; bid_level_2_order_counts := bid_level_2_order_counts_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_3_order_counts := ask_level_3_order_counts_value; bid_level_3_order_counts := bid_level_3_order_counts_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_4_order_counts := ask_level_4_order_counts_value; bid_level_4_order_counts := bid_level_4_order_counts_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_5_order_counts := ask_level_5_order_counts_value; bid_level_5_order_counts := bid_level_5_order_counts_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; ask_price_valid_counts := ask_price_valid_counts_value; bid_price_valid_counts := bid_price_valid_counts_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 354.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 bound_47]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_47.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativesMarketOperationTsPlusQuoteFiveLevelsMessage.

  Module DerivativesMarketOperationTsPlusQuoteTenLevelsMessage.

    (** Derivatives Market Operation TS plus Quote (Ten levels). Per-issue session-state event followed by full ten-level quote state. *)
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
      upper_limit_of_dynamic_price_range : list byte;
      lower_limit_of_dynamic_price_range : list byte;
      ask_level_1_price : list byte;
      bid_level_1_price : list byte;
      ask_level_1_volume : list byte;
      bid_level_1_volume : list byte;
      ask_level_1_order_counts : list byte;
      bid_level_1_order_counts : list byte;
      ask_level_2_price : list byte;
      bid_level_2_price : list byte;
      ask_level_2_volume : list byte;
      bid_level_2_volume : list byte;
      ask_level_2_order_counts : list byte;
      bid_level_2_order_counts : list byte;
      ask_level_3_price : list byte;
      bid_level_3_price : list byte;
      ask_level_3_volume : list byte;
      bid_level_3_volume : list byte;
      ask_level_3_order_counts : list byte;
      bid_level_3_order_counts : list byte;
      ask_level_4_price : list byte;
      bid_level_4_price : list byte;
      ask_level_4_volume : list byte;
      bid_level_4_volume : list byte;
      ask_level_4_order_counts : list byte;
      bid_level_4_order_counts : list byte;
      ask_level_5_price : list byte;
      bid_level_5_price : list byte;
      ask_level_5_volume : list byte;
      bid_level_5_volume : list byte;
      ask_level_5_order_counts : list byte;
      bid_level_5_order_counts : list byte;
      ask_level_6_price : list byte;
      bid_level_6_price : list byte;
      ask_level_6_volume : list byte;
      bid_level_6_volume : list byte;
      ask_level_6_order_counts : list byte;
      bid_level_6_order_counts : list byte;
      ask_level_7_price : list byte;
      bid_level_7_price : list byte;
      ask_level_7_volume : list byte;
      bid_level_7_volume : list byte;
      ask_level_7_order_counts : list byte;
      bid_level_7_order_counts : list byte;
      ask_level_8_price : list byte;
      bid_level_8_price : list byte;
      ask_level_8_volume : list byte;
      bid_level_8_volume : list byte;
      ask_level_8_order_counts : list byte;
      bid_level_8_order_counts : list byte;
      ask_level_9_price : list byte;
      bid_level_9_price : list byte;
      ask_level_9_volume : list byte;
      bid_level_9_volume : list byte;
      ask_level_9_order_counts : list byte;
      bid_level_9_order_counts : list byte;
      ask_level_10_price : list byte;
      bid_level_10_price : list byte;
      ask_level_10_volume : list byte;
      bid_level_10_volume : list byte;
      ask_level_10_order_counts : list byte;
      bid_level_10_order_counts : list byte;
      ask_total_volume : list byte;
      bid_total_volume : list byte;
      ask_price_valid_counts : list byte;
      bid_price_valid_counts : list byte;
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
      Datatypes.length (upper_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (lower_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (ask_level_1_price record) = 9 /\
      Datatypes.length (bid_level_1_price record) = 9 /\
      Datatypes.length (ask_level_1_volume record) = 9 /\
      Datatypes.length (bid_level_1_volume record) = 9 /\
      Datatypes.length (ask_level_1_order_counts record) = 5 /\
      Datatypes.length (bid_level_1_order_counts record) = 5 /\
      Datatypes.length (ask_level_2_price record) = 9 /\
      Datatypes.length (bid_level_2_price record) = 9 /\
      Datatypes.length (ask_level_2_volume record) = 9 /\
      Datatypes.length (bid_level_2_volume record) = 9 /\
      Datatypes.length (ask_level_2_order_counts record) = 5 /\
      Datatypes.length (bid_level_2_order_counts record) = 5 /\
      Datatypes.length (ask_level_3_price record) = 9 /\
      Datatypes.length (bid_level_3_price record) = 9 /\
      Datatypes.length (ask_level_3_volume record) = 9 /\
      Datatypes.length (bid_level_3_volume record) = 9 /\
      Datatypes.length (ask_level_3_order_counts record) = 5 /\
      Datatypes.length (bid_level_3_order_counts record) = 5 /\
      Datatypes.length (ask_level_4_price record) = 9 /\
      Datatypes.length (bid_level_4_price record) = 9 /\
      Datatypes.length (ask_level_4_volume record) = 9 /\
      Datatypes.length (bid_level_4_volume record) = 9 /\
      Datatypes.length (ask_level_4_order_counts record) = 5 /\
      Datatypes.length (bid_level_4_order_counts record) = 5 /\
      Datatypes.length (ask_level_5_price record) = 9 /\
      Datatypes.length (bid_level_5_price record) = 9 /\
      Datatypes.length (ask_level_5_volume record) = 9 /\
      Datatypes.length (bid_level_5_volume record) = 9 /\
      Datatypes.length (ask_level_5_order_counts record) = 5 /\
      Datatypes.length (bid_level_5_order_counts record) = 5 /\
      Datatypes.length (ask_level_6_price record) = 9 /\
      Datatypes.length (bid_level_6_price record) = 9 /\
      Datatypes.length (ask_level_6_volume record) = 9 /\
      Datatypes.length (bid_level_6_volume record) = 9 /\
      Datatypes.length (ask_level_6_order_counts record) = 5 /\
      Datatypes.length (bid_level_6_order_counts record) = 5 /\
      Datatypes.length (ask_level_7_price record) = 9 /\
      Datatypes.length (bid_level_7_price record) = 9 /\
      Datatypes.length (ask_level_7_volume record) = 9 /\
      Datatypes.length (bid_level_7_volume record) = 9 /\
      Datatypes.length (ask_level_7_order_counts record) = 5 /\
      Datatypes.length (bid_level_7_order_counts record) = 5 /\
      Datatypes.length (ask_level_8_price record) = 9 /\
      Datatypes.length (bid_level_8_price record) = 9 /\
      Datatypes.length (ask_level_8_volume record) = 9 /\
      Datatypes.length (bid_level_8_volume record) = 9 /\
      Datatypes.length (ask_level_8_order_counts record) = 5 /\
      Datatypes.length (bid_level_8_order_counts record) = 5 /\
      Datatypes.length (ask_level_9_price record) = 9 /\
      Datatypes.length (bid_level_9_price record) = 9 /\
      Datatypes.length (ask_level_9_volume record) = 9 /\
      Datatypes.length (bid_level_9_volume record) = 9 /\
      Datatypes.length (ask_level_9_order_counts record) = 5 /\
      Datatypes.length (bid_level_9_order_counts record) = 5 /\
      Datatypes.length (ask_level_10_price record) = 9 /\
      Datatypes.length (bid_level_10_price record) = 9 /\
      Datatypes.length (ask_level_10_volume record) = 9 /\
      Datatypes.length (bid_level_10_volume record) = 9 /\
      Datatypes.length (ask_level_10_order_counts record) = 5 /\
      Datatypes.length (bid_level_10_order_counts record) = 5 /\
      Datatypes.length (ask_total_volume record) = 9 /\
      Datatypes.length (bid_total_volume record) = 9 /\
      Datatypes.length (ask_price_valid_counts record) = 5 /\
      Datatypes.length (bid_price_valid_counts record) = 5 /\
      Datatypes.length (estimated_trading_price record) = 9 /\
      Datatypes.length (estimated_trading_volume record) = 9 /\
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
      encode_bytes 9 (upper_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (lower_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (ask_level_1_price record) ++
      encode_bytes 9 (bid_level_1_price record) ++
      encode_bytes 9 (ask_level_1_volume record) ++
      encode_bytes 9 (bid_level_1_volume record) ++
      encode_bytes 5 (ask_level_1_order_counts record) ++
      encode_bytes 5 (bid_level_1_order_counts record) ++
      encode_bytes 9 (ask_level_2_price record) ++
      encode_bytes 9 (bid_level_2_price record) ++
      encode_bytes 9 (ask_level_2_volume record) ++
      encode_bytes 9 (bid_level_2_volume record) ++
      encode_bytes 5 (ask_level_2_order_counts record) ++
      encode_bytes 5 (bid_level_2_order_counts record) ++
      encode_bytes 9 (ask_level_3_price record) ++
      encode_bytes 9 (bid_level_3_price record) ++
      encode_bytes 9 (ask_level_3_volume record) ++
      encode_bytes 9 (bid_level_3_volume record) ++
      encode_bytes 5 (ask_level_3_order_counts record) ++
      encode_bytes 5 (bid_level_3_order_counts record) ++
      encode_bytes 9 (ask_level_4_price record) ++
      encode_bytes 9 (bid_level_4_price record) ++
      encode_bytes 9 (ask_level_4_volume record) ++
      encode_bytes 9 (bid_level_4_volume record) ++
      encode_bytes 5 (ask_level_4_order_counts record) ++
      encode_bytes 5 (bid_level_4_order_counts record) ++
      encode_bytes 9 (ask_level_5_price record) ++
      encode_bytes 9 (bid_level_5_price record) ++
      encode_bytes 9 (ask_level_5_volume record) ++
      encode_bytes 9 (bid_level_5_volume record) ++
      encode_bytes 5 (ask_level_5_order_counts record) ++
      encode_bytes 5 (bid_level_5_order_counts record) ++
      encode_bytes 9 (ask_level_6_price record) ++
      encode_bytes 9 (bid_level_6_price record) ++
      encode_bytes 9 (ask_level_6_volume record) ++
      encode_bytes 9 (bid_level_6_volume record) ++
      encode_bytes 5 (ask_level_6_order_counts record) ++
      encode_bytes 5 (bid_level_6_order_counts record) ++
      encode_bytes 9 (ask_level_7_price record) ++
      encode_bytes 9 (bid_level_7_price record) ++
      encode_bytes 9 (ask_level_7_volume record) ++
      encode_bytes 9 (bid_level_7_volume record) ++
      encode_bytes 5 (ask_level_7_order_counts record) ++
      encode_bytes 5 (bid_level_7_order_counts record) ++
      encode_bytes 9 (ask_level_8_price record) ++
      encode_bytes 9 (bid_level_8_price record) ++
      encode_bytes 9 (ask_level_8_volume record) ++
      encode_bytes 9 (bid_level_8_volume record) ++
      encode_bytes 5 (ask_level_8_order_counts record) ++
      encode_bytes 5 (bid_level_8_order_counts record) ++
      encode_bytes 9 (ask_level_9_price record) ++
      encode_bytes 9 (bid_level_9_price record) ++
      encode_bytes 9 (ask_level_9_volume record) ++
      encode_bytes 9 (bid_level_9_volume record) ++
      encode_bytes 5 (ask_level_9_order_counts record) ++
      encode_bytes 5 (bid_level_9_order_counts record) ++
      encode_bytes 9 (ask_level_10_price record) ++
      encode_bytes 9 (bid_level_10_price record) ++
      encode_bytes 9 (ask_level_10_volume record) ++
      encode_bytes 9 (bid_level_10_volume record) ++
      encode_bytes 5 (ask_level_10_order_counts record) ++
      encode_bytes 5 (bid_level_10_order_counts record) ++
      encode_bytes 9 (ask_total_volume record) ++
      encode_bytes 9 (bid_total_volume record) ++
      encode_bytes 5 (ask_price_valid_counts record) ++
      encode_bytes 5 (bid_price_valid_counts record) ++
      encode_bytes 9 (estimated_trading_price record) ++
      encode_bytes 9 (estimated_trading_volume record) ++
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
                                          match decode_bytes 9 bytes with
                                          | None => None
                                          | Some (upper_limit_of_dynamic_price_range_value, bytes) =>
                                              match decode_bytes 9 bytes with
                                              | None => None
                                              | Some (lower_limit_of_dynamic_price_range_value, bytes) =>
                                                  match decode_bytes 9 bytes with
                                                  | None => None
                                                  | Some (ask_level_1_price_value, bytes) =>
                                                      match decode_bytes 9 bytes with
                                                      | None => None
                                                      | Some (bid_level_1_price_value, bytes) =>
                                                          match decode_bytes 9 bytes with
                                                          | None => None
                                                          | Some (ask_level_1_volume_value, bytes) =>
                                                              match decode_bytes 9 bytes with
                                                              | None => None
                                                              | Some (bid_level_1_volume_value, bytes) =>
                                                                  match decode_bytes 5 bytes with
                                                                  | None => None
                                                                  | Some (ask_level_1_order_counts_value, bytes) =>
                                                                      match decode_bytes 5 bytes with
                                                                      | None => None
                                                                      | Some (bid_level_1_order_counts_value, bytes) =>
                                                                          match decode_bytes 9 bytes with
                                                                          | None => None
                                                                          | Some (ask_level_2_price_value, bytes) =>
                                                                              match decode_bytes 9 bytes with
                                                                              | None => None
                                                                              | Some (bid_level_2_price_value, bytes) =>
                                                                                  match decode_bytes 9 bytes with
                                                                                  | None => None
                                                                                  | Some (ask_level_2_volume_value, bytes) =>
                                                                                      match decode_bytes 9 bytes with
                                                                                      | None => None
                                                                                      | Some (bid_level_2_volume_value, bytes) =>
                                                                                          match decode_bytes 5 bytes with
                                                                                          | None => None
                                                                                          | Some (ask_level_2_order_counts_value, bytes) =>
                                                                                              match decode_bytes 5 bytes with
                                                                                              | None => None
                                                                                              | Some (bid_level_2_order_counts_value, bytes) =>
                                                                                                  match decode_bytes 9 bytes with
                                                                                                  | None => None
                                                                                                  | Some (ask_level_3_price_value, bytes) =>
                                                                                                      match decode_bytes 9 bytes with
                                                                                                      | None => None
                                                                                                      | Some (bid_level_3_price_value, bytes) =>
                                                                                                          match decode_bytes 9 bytes with
                                                                                                          | None => None
                                                                                                          | Some (ask_level_3_volume_value, bytes) =>
                                                                                                              match decode_bytes 9 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bid_level_3_volume_value, bytes) =>
                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (ask_level_3_order_counts_value, bytes) =>
                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (bid_level_3_order_counts_value, bytes) =>
                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (ask_level_4_price_value, bytes) =>
                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (bid_level_4_price_value, bytes) =>
                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (ask_level_4_volume_value, bytes) =>
                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (bid_level_4_volume_value, bytes) =>
                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (ask_level_4_order_counts_value, bytes) =>
                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (bid_level_4_order_counts_value, bytes) =>
                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (ask_level_5_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (bid_level_5_price_value, bytes) =>
                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (ask_level_5_volume_value, bytes) =>
                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (bid_level_5_volume_value, bytes) =>
                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (ask_level_5_order_counts_value, bytes) =>
                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (bid_level_5_order_counts_value, bytes) =>
                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (ask_level_6_price_value, bytes) =>
                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (bid_level_6_price_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (ask_level_6_volume_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (bid_level_6_volume_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (ask_level_6_order_counts_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (bid_level_6_order_counts_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (ask_level_7_price_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (bid_level_7_price_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (ask_level_7_volume_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (bid_level_7_volume_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (ask_level_7_order_counts_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (bid_level_7_order_counts_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (ask_level_8_price_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (bid_level_8_price_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (ask_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (bid_level_8_volume_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (ask_level_8_order_counts_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (bid_level_8_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (ask_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (bid_level_9_price_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (ask_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (bid_level_9_volume_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (ask_level_9_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (bid_level_9_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (ask_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (bid_level_10_price_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (ask_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (bid_level_10_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (ask_level_10_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (bid_level_10_order_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (ask_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (bid_total_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (ask_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (bid_price_valid_counts_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (estimated_trading_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (estimated_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; board_event_id := board_event_id_value; start_time_of_a_board_event := start_time_of_a_board_event_value; board_event_group_code := board_event_group_code_value; upper_limit_of_dynamic_price_range := upper_limit_of_dynamic_price_range_value; lower_limit_of_dynamic_price_range := lower_limit_of_dynamic_price_range_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; ask_level_1_order_counts := ask_level_1_order_counts_value; bid_level_1_order_counts := bid_level_1_order_counts_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; ask_level_2_order_counts := ask_level_2_order_counts_value; bid_level_2_order_counts := bid_level_2_order_counts_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; ask_level_3_order_counts := ask_level_3_order_counts_value; bid_level_3_order_counts := bid_level_3_order_counts_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; ask_level_4_order_counts := ask_level_4_order_counts_value; bid_level_4_order_counts := bid_level_4_order_counts_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; ask_level_5_order_counts := ask_level_5_order_counts_value; bid_level_5_order_counts := bid_level_5_order_counts_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; ask_level_6_order_counts := ask_level_6_order_counts_value; bid_level_6_order_counts := bid_level_6_order_counts_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; ask_level_7_order_counts := ask_level_7_order_counts_value; bid_level_7_order_counts := bid_level_7_order_counts_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; ask_level_8_order_counts := ask_level_8_order_counts_value; bid_level_8_order_counts := bid_level_8_order_counts_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; ask_level_9_order_counts := ask_level_9_order_counts_value; bid_level_9_order_counts := bid_level_9_order_counts_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; ask_level_10_order_counts := ask_level_10_order_counts_value; bid_level_10_order_counts := bid_level_10_order_counts_value; ask_total_volume := ask_total_volume_value; bid_total_volume := bid_total_volume_value; ask_price_valid_counts := ask_price_valid_counts_value; bid_price_valid_counts := bid_price_valid_counts_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 584.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 bound_77]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_77.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativesMarketOperationTsPlusQuoteTenLevelsMessage.

  Module DerivativesNegotiatedTradeMessage.

    (** Derivatives Negotiated Trade Data. Off-book negotiated trades for futures and options. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      total_accumulated_trading_volume : list byte;
      total_accumulated_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (total_accumulated_trading_volume record) = 15 /\
      Datatypes.length (total_accumulated_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
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
              | Some (total_accumulated_trading_volume_value, bytes) =>
                  match decode_bytes 22 bytes with
                  | None => None
                  | Some (total_accumulated_trading_value_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; total_accumulated_trading_volume := total_accumulated_trading_volume_value; total_accumulated_trading_value := total_accumulated_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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

  End DerivativesNegotiatedTradeMessage.

  Module DerivativesMarketOperationTsMessage.

    (** Derivatives Market Operation TS. Per-issue session-state events for futures, options, and other derivatives. *)
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

  End DerivativesMarketOperationTsMessage.

  Module DerivativesIssueClosingMessage.

    (** Derivatives Issue Closing. Per-issue closing event for futures and options. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      closing_price : list byte;
      closing_price_type_code : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (closing_price record) = 9 /\
      Datatypes.length (closing_price_type_code record) = 1 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 9 (closing_price record) ++
      encode_bytes 1 (closing_price_type_code record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
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
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (closing_price_type_code_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (accumulated_trading_volume_value, bytes) =>
                                  match decode_bytes 22 bytes with
                                  | None => None
                                  | Some (accumulated_trading_value_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (end_keyword_value, bytes) =>
                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; closing_price := closing_price_value; closing_price_type_code := closing_price_type_code_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 73.
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

  End DerivativesIssueClosingMessage.

  Module DerivativesMarketOperationScheduleMessage.

    (** Derivatives Market Operation Schedule. Session-level schedule and configuration changes. *)
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

  End DerivativesMarketOperationScheduleMessage.

  Module DerivativesDynamicUpperLowerLimitMessage.

    (** Derivatives Applying/Removing Dynamic Upper/Lower Limit. Per-issue dynamic price-limit application or removal. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      processing_time_of_trading_system : list byte;
      dynamic_price_limit_type_code : list byte;
      upper_limit_of_dynamic_price_range : list byte;
      lower_limit_of_dynamic_price_range : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (dynamic_price_limit_type_code record) = 1 /\
      Datatypes.length (upper_limit_of_dynamic_price_range record) = 9 /\
      Datatypes.length (lower_limit_of_dynamic_price_range record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 1 (dynamic_price_limit_type_code record) ++
      encode_bytes 9 (upper_limit_of_dynamic_price_range record) ++
      encode_bytes 9 (lower_limit_of_dynamic_price_range record) ++
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
                          | Some (dynamic_price_limit_type_code_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (upper_limit_of_dynamic_price_range_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (lower_limit_of_dynamic_price_range_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (end_keyword_value, bytes) =>
                                          Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; processing_time_of_trading_system := processing_time_of_trading_system_value; dynamic_price_limit_type_code := dynamic_price_limit_type_code_value; upper_limit_of_dynamic_price_range := upper_limit_of_dynamic_price_range_value; lower_limit_of_dynamic_price_range := lower_limit_of_dynamic_price_range_value; end_keyword := end_keyword_value |}, bytes)
                                      end
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

  End DerivativesDynamicUpperLowerLimitMessage.

  Module DerivativesPriceLimitRangeIncreaseMessage.

    (** Derivatives Increasing Price Limit Range. Per-issue price-limit range expansion event. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      the_time_imposing_a_price_limit : list byte;
      price_limit_expansion_upper_limit : list byte;
      price_limit_expansion_lower_limit : list byte;
      upper_limit_price : list byte;
      lower_limit_price : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (the_time_imposing_a_price_limit record) = 9 /\
      Datatypes.length (price_limit_expansion_upper_limit record) = 2 /\
      Datatypes.length (price_limit_expansion_lower_limit record) = 2 /\
      Datatypes.length (upper_limit_price record) = 9 /\
      Datatypes.length (lower_limit_price record) = 9 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 9 (the_time_imposing_a_price_limit record) ++
      encode_bytes 2 (price_limit_expansion_upper_limit record) ++
      encode_bytes 2 (price_limit_expansion_lower_limit record) ++
      encode_bytes 9 (upper_limit_price record) ++
      encode_bytes 9 (lower_limit_price record) ++
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
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (the_time_imposing_a_price_limit_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (price_limit_expansion_upper_limit_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (price_limit_expansion_lower_limit_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (upper_limit_price_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (lower_limit_price_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (end_keyword_value, bytes) =>
                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; the_time_imposing_a_price_limit := the_time_imposing_a_price_limit_value; price_limit_expansion_upper_limit := price_limit_expansion_upper_limit_value; price_limit_expansion_lower_limit := price_limit_expansion_lower_limit_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; end_keyword := end_keyword_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
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

  End DerivativesPriceLimitRangeIncreaseMessage.

  Module DerivativesQuantityAllocationMessage.

    (** Derivatives Quantity Allocation. Reports the quantity allocated to each price level at a single price trade match. *)
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

  End DerivativesQuantityAllocationMessage.

  Module DerivativesGroupOrderAcceptanceHaltMessage.

    (** Derivatives Group Order Acceptance Halt/Release. Matching engine group-order halt and release events for futures and options. *)
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

  End DerivativesGroupOrderAcceptanceHaltMessage.

  Module DerivativesBatchDataMessage.

    (** Derivatives Batch Data. Comprehensive per-issue reference data dumped at start-of-day for futures, options, and other derivatives. *)
    Record t := {
      message_sequence_number : list byte;
      total_number_of_instruments_of_the_contract : list byte;
      business_date : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      futures_options_type_code : list byte;
      product_id : list byte;
      abbreviated_issue_code : list byte;
      issue_name : list byte;
      abbreviated_issue_name : list byte;
      english_issue_name : list byte;
      abbreviated_issue_name_in_en : list byte;
      market_operation_product_id : list byte;
      listing_date : list byte;
      delisting_date : list byte;
      spread_type_code : list byte;
      payment_methods : list byte;
      direction_of_price_limit_expansion_type_code : list byte;
      final_stage_of_price_limit_expansion : list byte;
      upper_price_limit_1_st_stage : list byte;
      upper_price_limit_2_nd_stage : list byte;
      upper_price_limit_3_rd_stage : list byte;
      lower_price_limit_1_st_stage : list byte;
      lower_price_limit_2_nd_stage : list byte;
      lower_price_limit_3_rd_stage : list byte;
      base_price : list byte;
      underlying_asset_id : list byte;
      rights_execution_type_code : list byte;
      spread_composition_code : list byte;
      spread_issue_isin_1 : list byte;
      spread_issue_isin_2 : list byte;
      last_trading_date : list byte;
      last_payment_date : list byte;
      sequence_number_for_delivery_month : list byte;
      expiration_date : list byte;
      exercise_price : list byte;
      base_price_adjustment_type_code : list byte;
      trading_unit : list byte;
      trading_multiplier : list byte;
      type_of_liquidity_providing_lp : list byte;
      listing_type_code : list byte;
      atm : list byte;
      adjustment_reason_code : list byte;
      isin_of_underlying_asset : list byte;
      closing_price_of_underlying_asset : list byte;
      remaining_days : list byte;
      adjusted_base_price : list byte;
      base_price_type_code : list byte;
      base_price_for_trading_type_code : list byte;
      previous_days_adjusted_closing_price : list byte;
      block_trading_type_code : list byte;
      previous_days_bpmm : list byte;
      base_price_of_clearing_margins_type_code : list byte;
      theoretical_settlement_price : list byte;
      base_theoretical_price : list byte;
      previous_days_settlement_price : list byte;
      trading_halt : list byte;
      futures_circuit_breakers_upper_limit_price : list byte;
      futures_circuit_breakers_lower_limit_price : list byte;
      exercise_price_for_displaying_not_for_trading : list byte;
      atm_type_code : list byte;
      last_trading_day : list byte;
      dividend_value_for_settlement_price : list byte;
      yesterdays_closing_price : list byte;
      yesterdays_closing_price_type_code : list byte;
      previous_days_opening_price : list byte;
      previous_days_high_price : list byte;
      previous_days_low_price : list byte;
      the_first_trading_date : list byte;
      the_last_trading_time : list byte;
      settlement_price_type_code : list byte;
      disparate_ratio : list byte;
      previous_days_open_interest : list byte;
      previous_days_best_ask : list byte;
      previous_days_best_bid : list byte;
      implied_volatility : list byte;
      the_highest_premium_of_the_lifetime : list byte;
      the_lowest_premium_of_the_lifetime : list byte;
      the_highest_premium_in_a_year : list byte;
      the_lowest_premium_in_a_year : list byte;
      the_date_of_the_highest_premium_of_the_lifetime : list byte;
      the_date_of_the_lowest_premium_of_the_lifetime : list byte;
      the_date_of_the_highest_premium_in_a_year : list byte;
      the_date_of_the_lowest_premium_in_a_year : list byte;
      number_of_listing_days_per_year : list byte;
      number_of_trading_days_per_month : list byte;
      number_of_trading_days_per_year : list byte;
      number_of_previous_days_trading : list byte;
      yesterdays_accumulated_trading_amount : list byte;
      yesterdays_accumulated_trading_value : list byte;
      previous_days_total_accumulated_trading_volume : list byte;
      previous_days_total_accumulated_trading_value : list byte;
      interest_rate : list byte;
      open_interest_limit_quantity : list byte;
      underlying_asset_product_id : list byte;
      offset_rate_of_asset_group : list byte;
      limit_order_permission_type_code : list byte;
      market_price_order_permission_type_code : list byte;
      conditioned_order_permission_type_code : list byte;
      best_favorable_order_permission_type_code : list byte;
      efp_trading_item : list byte;
      flex_trading_item : list byte;
      efp_trading_volume : list byte;
      efp_trading_value : list byte;
      market_holidays : list byte;
      limitation_of_dynamic_price : list byte;
      gap_between_upper_limit_price_of_dynamic_price_and_trading_value : list byte;
      gap_between_lower_limit_price_of_dynamic_price_and_trading_value : list byte;
      underlying_asset_market_id : list byte;
      upper_limit_quantity : list byte;
      lower_limit_quantity : list byte;
      upper_limit_quantity_for_block_trade : list byte;
      lower_limit_quantity_for_block_trade : list byte;
      base_product_id : list byte;
      subsidiary_product_id : list byte;
      number_of_issues_for_base_product : list byte;
      number_of_issues_for_subsidiary_product : list byte;
      settlement_week : list byte;
      suspended_stocks : list byte;
      designation_date_for_suspended_stocks : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (total_number_of_instruments_of_the_contract record) = 6 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (futures_options_type_code record) = 1 /\
      Datatypes.length (product_id record) = 11 /\
      Datatypes.length (abbreviated_issue_code record) = 9 /\
      Datatypes.length (issue_name record) = 80 /\
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (english_issue_name record) = 80 /\
      Datatypes.length (abbreviated_issue_name_in_en record) = 40 /\
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (listing_date record) = 8 /\
      Datatypes.length (delisting_date record) = 8 /\
      Datatypes.length (spread_type_code record) = 1 /\
      Datatypes.length (payment_methods record) = 1 /\
      Datatypes.length (direction_of_price_limit_expansion_type_code record) = 1 /\
      Datatypes.length (final_stage_of_price_limit_expansion record) = 3 /\
      Datatypes.length (upper_price_limit_1_st_stage record) = 11 /\
      Datatypes.length (upper_price_limit_2_nd_stage record) = 11 /\
      Datatypes.length (upper_price_limit_3_rd_stage record) = 11 /\
      Datatypes.length (lower_price_limit_1_st_stage record) = 11 /\
      Datatypes.length (lower_price_limit_2_nd_stage record) = 11 /\
      Datatypes.length (lower_price_limit_3_rd_stage record) = 11 /\
      Datatypes.length (base_price record) = 11 /\
      Datatypes.length (underlying_asset_id record) = 3 /\
      Datatypes.length (rights_execution_type_code record) = 1 /\
      Datatypes.length (spread_composition_code record) = 2 /\
      Datatypes.length (spread_issue_isin_1 record) = 12 /\
      Datatypes.length (spread_issue_isin_2 record) = 12 /\
      Datatypes.length (last_trading_date record) = 8 /\
      Datatypes.length (last_payment_date record) = 8 /\
      Datatypes.length (sequence_number_for_delivery_month record) = 3 /\
      Datatypes.length (expiration_date record) = 8 /\
      Datatypes.length (exercise_price record) = 18 /\
      Datatypes.length (base_price_adjustment_type_code record) = 1 /\
      Datatypes.length (trading_unit record) = 22 /\
      Datatypes.length (trading_multiplier record) = 22 /\
      Datatypes.length (type_of_liquidity_providing_lp record) = 1 /\
      Datatypes.length (listing_type_code record) = 1 /\
      Datatypes.length (atm record) = 11 /\
      Datatypes.length (adjustment_reason_code record) = 2 /\
      Datatypes.length (isin_of_underlying_asset record) = 12 /\
      Datatypes.length (closing_price_of_underlying_asset record) = 11 /\
      Datatypes.length (remaining_days record) = 8 /\
      Datatypes.length (adjusted_base_price record) = 18 /\
      Datatypes.length (base_price_type_code record) = 2 /\
      Datatypes.length (base_price_for_trading_type_code record) = 1 /\
      Datatypes.length (previous_days_adjusted_closing_price record) = 18 /\
      Datatypes.length (block_trading_type_code record) = 1 /\
      Datatypes.length (previous_days_bpmm record) = 23 /\
      Datatypes.length (base_price_of_clearing_margins_type_code record) = 2 /\
      Datatypes.length (theoretical_settlement_price record) = 16 /\
      Datatypes.length (base_theoretical_price record) = 16 /\
      Datatypes.length (previous_days_settlement_price record) = 18 /\
      Datatypes.length (trading_halt record) = 1 /\
      Datatypes.length (futures_circuit_breakers_upper_limit_price record) = 11 /\
      Datatypes.length (futures_circuit_breakers_lower_limit_price record) = 11 /\
      Datatypes.length (exercise_price_for_displaying_not_for_trading record) = 18 /\
      Datatypes.length (atm_type_code record) = 1 /\
      Datatypes.length (last_trading_day record) = 1 /\
      Datatypes.length (dividend_value_for_settlement_price record) = 16 /\
      Datatypes.length (yesterdays_closing_price record) = 11 /\
      Datatypes.length (yesterdays_closing_price_type_code record) = 1 /\
      Datatypes.length (previous_days_opening_price record) = 11 /\
      Datatypes.length (previous_days_high_price record) = 11 /\
      Datatypes.length (previous_days_low_price record) = 11 /\
      Datatypes.length (the_first_trading_date record) = 8 /\
      Datatypes.length (the_last_trading_time record) = 9 /\
      Datatypes.length (settlement_price_type_code record) = 2 /\
      Datatypes.length (disparate_ratio record) = 13 /\
      Datatypes.length (previous_days_open_interest record) = 12 /\
      Datatypes.length (previous_days_best_ask record) = 11 /\
      Datatypes.length (previous_days_best_bid record) = 11 /\
      Datatypes.length (implied_volatility record) = 11 /\
      Datatypes.length (the_highest_premium_of_the_lifetime record) = 11 /\
      Datatypes.length (the_lowest_premium_of_the_lifetime record) = 11 /\
      Datatypes.length (the_highest_premium_in_a_year record) = 11 /\
      Datatypes.length (the_lowest_premium_in_a_year record) = 11 /\
      Datatypes.length (the_date_of_the_highest_premium_of_the_lifetime record) = 8 /\
      Datatypes.length (the_date_of_the_lowest_premium_of_the_lifetime record) = 8 /\
      Datatypes.length (the_date_of_the_highest_premium_in_a_year record) = 8 /\
      Datatypes.length (the_date_of_the_lowest_premium_in_a_year record) = 8 /\
      Datatypes.length (number_of_listing_days_per_year record) = 8 /\
      Datatypes.length (number_of_trading_days_per_month record) = 8 /\
      Datatypes.length (number_of_trading_days_per_year record) = 8 /\
      Datatypes.length (number_of_previous_days_trading record) = 15 /\
      Datatypes.length (yesterdays_accumulated_trading_amount record) = 12 /\
      Datatypes.length (yesterdays_accumulated_trading_value record) = 22 /\
      Datatypes.length (previous_days_total_accumulated_trading_volume record) = 15 /\
      Datatypes.length (previous_days_total_accumulated_trading_value record) = 22 /\
      Datatypes.length (interest_rate record) = 11 /\
      Datatypes.length (open_interest_limit_quantity record) = 15 /\
      Datatypes.length (underlying_asset_product_id record) = 4 /\
      Datatypes.length (offset_rate_of_asset_group record) = 11 /\
      Datatypes.length (limit_order_permission_type_code record) = 5 /\
      Datatypes.length (market_price_order_permission_type_code record) = 5 /\
      Datatypes.length (conditioned_order_permission_type_code record) = 5 /\
      Datatypes.length (best_favorable_order_permission_type_code record) = 5 /\
      Datatypes.length (efp_trading_item record) = 1 /\
      Datatypes.length (flex_trading_item record) = 1 /\
      Datatypes.length (efp_trading_volume record) = 12 /\
      Datatypes.length (efp_trading_value record) = 22 /\
      Datatypes.length (market_holidays record) = 1 /\
      Datatypes.length (limitation_of_dynamic_price record) = 1 /\
      Datatypes.length (gap_between_upper_limit_price_of_dynamic_price_and_trading_value record) = 11 /\
      Datatypes.length (gap_between_lower_limit_price_of_dynamic_price_and_trading_value record) = 11 /\
      Datatypes.length (underlying_asset_market_id record) = 3 /\
      Datatypes.length (upper_limit_quantity record) = 23 /\
      Datatypes.length (lower_limit_quantity record) = 23 /\
      Datatypes.length (upper_limit_quantity_for_block_trade record) = 23 /\
      Datatypes.length (lower_limit_quantity_for_block_trade record) = 23 /\
      Datatypes.length (base_product_id record) = 11 /\
      Datatypes.length (subsidiary_product_id record) = 11 /\
      Datatypes.length (number_of_issues_for_base_product record) = 6 /\
      Datatypes.length (number_of_issues_for_subsidiary_product record) = 6 /\
      Datatypes.length (settlement_week record) = 2 /\
      Datatypes.length (suspended_stocks record) = 1 /\
      Datatypes.length (designation_date_for_suspended_stocks record) = 8 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 6 (total_number_of_instruments_of_the_contract record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 1 (futures_options_type_code record) ++
      encode_bytes 11 (product_id record) ++
      encode_bytes 9 (abbreviated_issue_code record) ++
      encode_bytes 80 (issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 80 (english_issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name_in_en record) ++
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 8 (listing_date record) ++
      encode_bytes 8 (delisting_date record) ++
      encode_bytes 1 (spread_type_code record) ++
      encode_bytes 1 (payment_methods record) ++
      encode_bytes 1 (direction_of_price_limit_expansion_type_code record) ++
      encode_bytes 3 (final_stage_of_price_limit_expansion record) ++
      encode_bytes 11 (upper_price_limit_1_st_stage record) ++
      encode_bytes 11 (upper_price_limit_2_nd_stage record) ++
      encode_bytes 11 (upper_price_limit_3_rd_stage record) ++
      encode_bytes 11 (lower_price_limit_1_st_stage record) ++
      encode_bytes 11 (lower_price_limit_2_nd_stage record) ++
      encode_bytes 11 (lower_price_limit_3_rd_stage record) ++
      encode_bytes 11 (base_price record) ++
      encode_bytes 3 (underlying_asset_id record) ++
      encode_bytes 1 (rights_execution_type_code record) ++
      encode_bytes 2 (spread_composition_code record) ++
      encode_bytes 12 (spread_issue_isin_1 record) ++
      encode_bytes 12 (spread_issue_isin_2 record) ++
      encode_bytes 8 (last_trading_date record) ++
      encode_bytes 8 (last_payment_date record) ++
      encode_bytes 3 (sequence_number_for_delivery_month record) ++
      encode_bytes 8 (expiration_date record) ++
      encode_bytes 18 (exercise_price record) ++
      encode_bytes 1 (base_price_adjustment_type_code record) ++
      encode_bytes 22 (trading_unit record) ++
      encode_bytes 22 (trading_multiplier record) ++
      encode_bytes 1 (type_of_liquidity_providing_lp record) ++
      encode_bytes 1 (listing_type_code record) ++
      encode_bytes 11 (atm record) ++
      encode_bytes 2 (adjustment_reason_code record) ++
      encode_bytes 12 (isin_of_underlying_asset record) ++
      encode_bytes 11 (closing_price_of_underlying_asset record) ++
      encode_bytes 8 (remaining_days record) ++
      encode_bytes 18 (adjusted_base_price record) ++
      encode_bytes 2 (base_price_type_code record) ++
      encode_bytes 1 (base_price_for_trading_type_code record) ++
      encode_bytes 18 (previous_days_adjusted_closing_price record) ++
      encode_bytes 1 (block_trading_type_code record) ++
      encode_bytes 23 (previous_days_bpmm record) ++
      encode_bytes 2 (base_price_of_clearing_margins_type_code record) ++
      encode_bytes 16 (theoretical_settlement_price record) ++
      encode_bytes 16 (base_theoretical_price record) ++
      encode_bytes 18 (previous_days_settlement_price record) ++
      encode_bytes 1 (trading_halt record) ++
      encode_bytes 11 (futures_circuit_breakers_upper_limit_price record) ++
      encode_bytes 11 (futures_circuit_breakers_lower_limit_price record) ++
      encode_bytes 18 (exercise_price_for_displaying_not_for_trading record) ++
      encode_bytes 1 (atm_type_code record) ++
      encode_bytes 1 (last_trading_day record) ++
      encode_bytes 16 (dividend_value_for_settlement_price record) ++
      encode_bytes 11 (yesterdays_closing_price record) ++
      encode_bytes 1 (yesterdays_closing_price_type_code record) ++
      encode_bytes 11 (previous_days_opening_price record) ++
      encode_bytes 11 (previous_days_high_price record) ++
      encode_bytes 11 (previous_days_low_price record) ++
      encode_bytes 8 (the_first_trading_date record) ++
      encode_bytes 9 (the_last_trading_time record) ++
      encode_bytes 2 (settlement_price_type_code record) ++
      encode_bytes 13 (disparate_ratio record) ++
      encode_bytes 12 (previous_days_open_interest record) ++
      encode_bytes 11 (previous_days_best_ask record) ++
      encode_bytes 11 (previous_days_best_bid record) ++
      encode_bytes 11 (implied_volatility record) ++
      encode_bytes 11 (the_highest_premium_of_the_lifetime record) ++
      encode_bytes 11 (the_lowest_premium_of_the_lifetime record) ++
      encode_bytes 11 (the_highest_premium_in_a_year record) ++
      encode_bytes 11 (the_lowest_premium_in_a_year record) ++
      encode_bytes 8 (the_date_of_the_highest_premium_of_the_lifetime record) ++
      encode_bytes 8 (the_date_of_the_lowest_premium_of_the_lifetime record) ++
      encode_bytes 8 (the_date_of_the_highest_premium_in_a_year record) ++
      encode_bytes 8 (the_date_of_the_lowest_premium_in_a_year record) ++
      encode_bytes 8 (number_of_listing_days_per_year record) ++
      encode_bytes 8 (number_of_trading_days_per_month record) ++
      encode_bytes 8 (number_of_trading_days_per_year record) ++
      encode_bytes 15 (number_of_previous_days_trading record) ++
      encode_bytes 12 (yesterdays_accumulated_trading_amount record) ++
      encode_bytes 22 (yesterdays_accumulated_trading_value record) ++
      encode_bytes 15 (previous_days_total_accumulated_trading_volume record) ++
      encode_bytes 22 (previous_days_total_accumulated_trading_value record) ++
      encode_bytes 11 (interest_rate record) ++
      encode_bytes 15 (open_interest_limit_quantity record) ++
      encode_bytes 4 (underlying_asset_product_id record) ++
      encode_bytes 11 (offset_rate_of_asset_group record) ++
      encode_bytes 5 (limit_order_permission_type_code record) ++
      encode_bytes 5 (market_price_order_permission_type_code record) ++
      encode_bytes 5 (conditioned_order_permission_type_code record) ++
      encode_bytes 5 (best_favorable_order_permission_type_code record) ++
      encode_bytes 1 (efp_trading_item record) ++
      encode_bytes 1 (flex_trading_item record) ++
      encode_bytes 12 (efp_trading_volume record) ++
      encode_bytes 22 (efp_trading_value record) ++
      encode_bytes 1 (market_holidays record) ++
      encode_bytes 1 (limitation_of_dynamic_price record) ++
      encode_bytes 11 (gap_between_upper_limit_price_of_dynamic_price_and_trading_value record) ++
      encode_bytes 11 (gap_between_lower_limit_price_of_dynamic_price_and_trading_value record) ++
      encode_bytes 3 (underlying_asset_market_id record) ++
      encode_bytes 23 (upper_limit_quantity record) ++
      encode_bytes 23 (lower_limit_quantity record) ++
      encode_bytes 23 (upper_limit_quantity_for_block_trade record) ++
      encode_bytes 23 (lower_limit_quantity_for_block_trade record) ++
      encode_bytes 11 (base_product_id record) ++
      encode_bytes 11 (subsidiary_product_id record) ++
      encode_bytes 6 (number_of_issues_for_base_product record) ++
      encode_bytes 6 (number_of_issues_for_subsidiary_product record) ++
      encode_bytes 2 (settlement_week record) ++
      encode_bytes 1 (suspended_stocks record) ++
      encode_bytes 8 (designation_date_for_suspended_stocks record) ++
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
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (futures_options_type_code_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (product_id_value, bytes) =>
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
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (listing_date_value, bytes) =>
                                                              match decode_bytes 8 bytes with
                                                              | None => None
                                                              | Some (delisting_date_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (spread_type_code_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (payment_methods_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (direction_of_price_limit_expansion_type_code_value, bytes) =>
                                                                              match decode_bytes 3 bytes with
                                                                              | None => None
                                                                              | Some (final_stage_of_price_limit_expansion_value, bytes) =>
                                                                                  match decode_bytes 11 bytes with
                                                                                  | None => None
                                                                                  | Some (upper_price_limit_1_st_stage_value, bytes) =>
                                                                                      match decode_bytes 11 bytes with
                                                                                      | None => None
                                                                                      | Some (upper_price_limit_2_nd_stage_value, bytes) =>
                                                                                          match decode_bytes 11 bytes with
                                                                                          | None => None
                                                                                          | Some (upper_price_limit_3_rd_stage_value, bytes) =>
                                                                                              match decode_bytes 11 bytes with
                                                                                              | None => None
                                                                                              | Some (lower_price_limit_1_st_stage_value, bytes) =>
                                                                                                  match decode_bytes 11 bytes with
                                                                                                  | None => None
                                                                                                  | Some (lower_price_limit_2_nd_stage_value, bytes) =>
                                                                                                      match decode_bytes 11 bytes with
                                                                                                      | None => None
                                                                                                      | Some (lower_price_limit_3_rd_stage_value, bytes) =>
                                                                                                          match decode_bytes 11 bytes with
                                                                                                          | None => None
                                                                                                          | Some (base_price_value, bytes) =>
                                                                                                              match decode_bytes 3 bytes with
                                                                                                              | None => None
                                                                                                              | Some (underlying_asset_id_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (rights_execution_type_code_value, bytes) =>
                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (spread_composition_code_value, bytes) =>
                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (spread_issue_isin_1_value, bytes) =>
                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (spread_issue_isin_2_value, bytes) =>
                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (last_trading_date_value, bytes) =>
                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (last_payment_date_value, bytes) =>
                                                                                                                                          match decode_bytes 3 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (sequence_number_for_delivery_month_value, bytes) =>
                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (expiration_date_value, bytes) =>
                                                                                                                                                  match decode_bytes 18 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (exercise_price_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (base_price_adjustment_type_code_value, bytes) =>
                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (trading_unit_value, bytes) =>
                                                                                                                                                              match decode_bytes 22 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (trading_multiplier_value, bytes) =>
                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (type_of_liquidity_providing_lp_value, bytes) =>
                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (listing_type_code_value, bytes) =>
                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (atm_value, bytes) =>
                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (adjustment_reason_code_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (isin_of_underlying_asset_value, bytes) =>
                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (closing_price_of_underlying_asset_value, bytes) =>
                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (remaining_days_value, bytes) =>
                                                                                                                                                                                              match decode_bytes 18 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (adjusted_base_price_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 2 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (base_price_type_code_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (base_price_for_trading_type_code_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 18 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (previous_days_adjusted_closing_price_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (block_trading_type_code_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 23 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (previous_days_bpmm_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 2 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (base_price_of_clearing_margins_type_code_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 16 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (theoretical_settlement_price_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 16 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (base_theoretical_price_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 18 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (previous_days_settlement_price_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (trading_halt_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (futures_circuit_breakers_upper_limit_price_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (futures_circuit_breakers_lower_limit_price_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 18 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (exercise_price_for_displaying_not_for_trading_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (atm_type_code_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (last_trading_day_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 16 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (dividend_value_for_settlement_price_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (yesterdays_closing_price_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (yesterdays_closing_price_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (previous_days_opening_price_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (previous_days_high_price_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (previous_days_low_price_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (the_first_trading_date_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 9 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (the_last_trading_time_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (settlement_price_type_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 13 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (disparate_ratio_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (previous_days_open_interest_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (previous_days_best_ask_value, bytes) =>
                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                              | Some (previous_days_best_bid_value, bytes) =>
                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                  | Some (implied_volatility_value, bytes) =>
                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                      | Some (the_highest_premium_of_the_lifetime_value, bytes) =>
                                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                          | Some (the_lowest_premium_of_the_lifetime_value, bytes) =>
                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                              | Some (the_highest_premium_in_a_year_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                  | Some (the_lowest_premium_in_a_year_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                      | Some (the_date_of_the_highest_premium_of_the_lifetime_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                          | Some (the_date_of_the_lowest_premium_of_the_lifetime_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                              | Some (the_date_of_the_highest_premium_in_a_year_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                  | Some (the_date_of_the_lowest_premium_in_a_year_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (number_of_listing_days_per_year_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (number_of_trading_days_per_month_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (number_of_trading_days_per_year_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                  | Some (number_of_previous_days_trading_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                      | Some (yesterdays_accumulated_trading_amount_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                          | Some (yesterdays_accumulated_trading_value_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                              | Some (previous_days_total_accumulated_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                  | Some (previous_days_total_accumulated_trading_value_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                      | Some (interest_rate_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 15 bytes with
                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                          | Some (open_interest_limit_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                              | Some (underlying_asset_product_id_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                  | Some (offset_rate_of_asset_group_value, bytes) =>
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
                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (efp_trading_item_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (flex_trading_item_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (efp_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 22 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (efp_trading_value_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (market_holidays_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (limitation_of_dynamic_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (gap_between_upper_limit_price_of_dynamic_price_and_trading_value_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (gap_between_lower_limit_price_of_dynamic_price_and_trading_value_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 3 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (underlying_asset_market_id_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 23 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (upper_limit_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 23 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (lower_limit_quantity_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 23 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (upper_limit_quantity_for_block_trade_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 23 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (lower_limit_quantity_for_block_trade_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (base_product_id_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (subsidiary_product_id_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (number_of_issues_for_base_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 6 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (number_of_issues_for_subsidiary_product_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 2 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (settlement_week_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (suspended_stocks_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 8 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (designation_date_for_suspended_stocks_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          Some ({| message_sequence_number := message_sequence_number_value; total_number_of_instruments_of_the_contract := total_number_of_instruments_of_the_contract_value; business_date := business_date_value; isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; futures_options_type_code := futures_options_type_code_value; product_id := product_id_value; abbreviated_issue_code := abbreviated_issue_code_value; issue_name := issue_name_value; abbreviated_issue_name := abbreviated_issue_name_value; english_issue_name := english_issue_name_value; abbreviated_issue_name_in_en := abbreviated_issue_name_in_en_value; market_operation_product_id := market_operation_product_id_value; listing_date := listing_date_value; delisting_date := delisting_date_value; spread_type_code := spread_type_code_value; payment_methods := payment_methods_value; direction_of_price_limit_expansion_type_code := direction_of_price_limit_expansion_type_code_value; final_stage_of_price_limit_expansion := final_stage_of_price_limit_expansion_value; upper_price_limit_1_st_stage := upper_price_limit_1_st_stage_value; upper_price_limit_2_nd_stage := upper_price_limit_2_nd_stage_value; upper_price_limit_3_rd_stage := upper_price_limit_3_rd_stage_value; lower_price_limit_1_st_stage := lower_price_limit_1_st_stage_value; lower_price_limit_2_nd_stage := lower_price_limit_2_nd_stage_value; lower_price_limit_3_rd_stage := lower_price_limit_3_rd_stage_value; base_price := base_price_value; underlying_asset_id := underlying_asset_id_value; rights_execution_type_code := rights_execution_type_code_value; spread_composition_code := spread_composition_code_value; spread_issue_isin_1 := spread_issue_isin_1_value; spread_issue_isin_2 := spread_issue_isin_2_value; last_trading_date := last_trading_date_value; last_payment_date := last_payment_date_value; sequence_number_for_delivery_month := sequence_number_for_delivery_month_value; expiration_date := expiration_date_value; exercise_price := exercise_price_value; base_price_adjustment_type_code := base_price_adjustment_type_code_value; trading_unit := trading_unit_value; trading_multiplier := trading_multiplier_value; type_of_liquidity_providing_lp := type_of_liquidity_providing_lp_value; listing_type_code := listing_type_code_value; atm := atm_value; adjustment_reason_code := adjustment_reason_code_value; isin_of_underlying_asset := isin_of_underlying_asset_value; closing_price_of_underlying_asset := closing_price_of_underlying_asset_value; remaining_days := remaining_days_value; adjusted_base_price := adjusted_base_price_value; base_price_type_code := base_price_type_code_value; base_price_for_trading_type_code := base_price_for_trading_type_code_value; previous_days_adjusted_closing_price := previous_days_adjusted_closing_price_value; block_trading_type_code := block_trading_type_code_value; previous_days_bpmm := previous_days_bpmm_value; base_price_of_clearing_margins_type_code := base_price_of_clearing_margins_type_code_value; theoretical_settlement_price := theoretical_settlement_price_value; base_theoretical_price := base_theoretical_price_value; previous_days_settlement_price := previous_days_settlement_price_value; trading_halt := trading_halt_value; futures_circuit_breakers_upper_limit_price := futures_circuit_breakers_upper_limit_price_value; futures_circuit_breakers_lower_limit_price := futures_circuit_breakers_lower_limit_price_value; exercise_price_for_displaying_not_for_trading := exercise_price_for_displaying_not_for_trading_value; atm_type_code := atm_type_code_value; last_trading_day := last_trading_day_value; dividend_value_for_settlement_price := dividend_value_for_settlement_price_value; yesterdays_closing_price := yesterdays_closing_price_value; yesterdays_closing_price_type_code := yesterdays_closing_price_type_code_value; previous_days_opening_price := previous_days_opening_price_value; previous_days_high_price := previous_days_high_price_value; previous_days_low_price := previous_days_low_price_value; the_first_trading_date := the_first_trading_date_value; the_last_trading_time := the_last_trading_time_value; settlement_price_type_code := settlement_price_type_code_value; disparate_ratio := disparate_ratio_value; previous_days_open_interest := previous_days_open_interest_value; previous_days_best_ask := previous_days_best_ask_value; previous_days_best_bid := previous_days_best_bid_value; implied_volatility := implied_volatility_value; the_highest_premium_of_the_lifetime := the_highest_premium_of_the_lifetime_value; the_lowest_premium_of_the_lifetime := the_lowest_premium_of_the_lifetime_value; the_highest_premium_in_a_year := the_highest_premium_in_a_year_value; the_lowest_premium_in_a_year := the_lowest_premium_in_a_year_value; the_date_of_the_highest_premium_of_the_lifetime := the_date_of_the_highest_premium_of_the_lifetime_value; the_date_of_the_lowest_premium_of_the_lifetime := the_date_of_the_lowest_premium_of_the_lifetime_value; the_date_of_the_highest_premium_in_a_year := the_date_of_the_highest_premium_in_a_year_value; the_date_of_the_lowest_premium_in_a_year := the_date_of_the_lowest_premium_in_a_year_value; number_of_listing_days_per_year := number_of_listing_days_per_year_value; number_of_trading_days_per_month := number_of_trading_days_per_month_value; number_of_trading_days_per_year := number_of_trading_days_per_year_value; number_of_previous_days_trading := number_of_previous_days_trading_value; yesterdays_accumulated_trading_amount := yesterdays_accumulated_trading_amount_value; yesterdays_accumulated_trading_value := yesterdays_accumulated_trading_value_value; previous_days_total_accumulated_trading_volume := previous_days_total_accumulated_trading_volume_value; previous_days_total_accumulated_trading_value := previous_days_total_accumulated_trading_value_value; interest_rate := interest_rate_value; open_interest_limit_quantity := open_interest_limit_quantity_value; underlying_asset_product_id := underlying_asset_product_id_value; offset_rate_of_asset_group := offset_rate_of_asset_group_value; limit_order_permission_type_code := limit_order_permission_type_code_value; market_price_order_permission_type_code := market_price_order_permission_type_code_value; conditioned_order_permission_type_code := conditioned_order_permission_type_code_value; best_favorable_order_permission_type_code := best_favorable_order_permission_type_code_value; efp_trading_item := efp_trading_item_value; flex_trading_item := flex_trading_item_value; efp_trading_volume := efp_trading_volume_value; efp_trading_value := efp_trading_value_value; market_holidays := market_holidays_value; limitation_of_dynamic_price := limitation_of_dynamic_price_value; gap_between_upper_limit_price_of_dynamic_price_and_trading_value := gap_between_upper_limit_price_of_dynamic_price_and_trading_value_value; gap_between_lower_limit_price_of_dynamic_price_and_trading_value := gap_between_lower_limit_price_of_dynamic_price_and_trading_value_value; underlying_asset_market_id := underlying_asset_market_id_value; upper_limit_quantity := upper_limit_quantity_value; lower_limit_quantity := lower_limit_quantity_value; upper_limit_quantity_for_block_trade := upper_limit_quantity_for_block_trade_value; lower_limit_quantity_for_block_trade := lower_limit_quantity_for_block_trade_value; base_product_id := base_product_id_value; subsidiary_product_id := subsidiary_product_id_value; number_of_issues_for_base_product := number_of_issues_for_base_product_value; number_of_issues_for_subsidiary_product := number_of_issues_for_subsidiary_product_value; settlement_week := settlement_week_value; suspended_stocks := suspended_stocks_value; designation_date_for_suspended_stocks := designation_date_for_suspended_stocks_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1313.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 [bound_87 [bound_88 [bound_89 [bound_90 [bound_91 [bound_92 [bound_93 [bound_94 [bound_95 [bound_96 [bound_97 [bound_98 [bound_99 [bound_100 [bound_101 [bound_102 [bound_103 [bound_104 [bound_105 [bound_106 [bound_107 [bound_108 [bound_109 [bound_110 [bound_111 [bound_112 [bound_113 [bound_114 [bound_115 [bound_116 [bound_117 [bound_118 [bound_119 bound_120]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_120.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativesBatchDataMessage.

  Module EquityDerivativesAdjustmentDetailsMessage.

    (** Equity Derivatives Adjustment Details. Corporate-action and contract-spec adjustments to equity-derivatives positions. *)
    Record t := {
      message_sequence_number : list byte;
      business_date : list byte;
      isin_code : list byte;
      denominator_coefficient_of_adjustment : list byte;
      numerator_adjustment_of_coefficient : list byte;
      trading_multiplier_before_adjustment : list byte;
      trading_multiplier_after_adjustment_equity_options_10 : list byte;
      exercise_price_before_adjustment : list byte;
      exercise_price_after_adjustment : list byte;
      adjustment_coefficient_of_open_intetest_volumes_that_have_been_adjusted : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (denominator_coefficient_of_adjustment record) = 18 /\
      Datatypes.length (numerator_adjustment_of_coefficient record) = 18 /\
      Datatypes.length (trading_multiplier_before_adjustment record) = 22 /\
      Datatypes.length (trading_multiplier_after_adjustment_equity_options_10 record) = 22 /\
      Datatypes.length (exercise_price_before_adjustment record) = 18 /\
      Datatypes.length (exercise_price_after_adjustment record) = 18 /\
      Datatypes.length (adjustment_coefficient_of_open_intetest_volumes_that_have_been_adjusted record) = 6 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 18 (denominator_coefficient_of_adjustment record) ++
      encode_bytes 18 (numerator_adjustment_of_coefficient record) ++
      encode_bytes 22 (trading_multiplier_before_adjustment record) ++
      encode_bytes 22 (trading_multiplier_after_adjustment_equity_options_10 record) ++
      encode_bytes 18 (exercise_price_before_adjustment record) ++
      encode_bytes 18 (exercise_price_after_adjustment record) ++
      encode_bytes 6 (adjustment_coefficient_of_open_intetest_volumes_that_have_been_adjusted record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (business_date_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 18 bytes with
                  | None => None
                  | Some (denominator_coefficient_of_adjustment_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (numerator_adjustment_of_coefficient_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (trading_multiplier_before_adjustment_value, bytes) =>
                              match decode_bytes 22 bytes with
                              | None => None
                              | Some (trading_multiplier_after_adjustment_equity_options_10_value, bytes) =>
                                  match decode_bytes 18 bytes with
                                  | None => None
                                  | Some (exercise_price_before_adjustment_value, bytes) =>
                                      match decode_bytes 18 bytes with
                                      | None => None
                                      | Some (exercise_price_after_adjustment_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (adjustment_coefficient_of_open_intetest_volumes_that_have_been_adjusted_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (end_keyword_value, bytes) =>
                                                  Some ({| message_sequence_number := message_sequence_number_value; business_date := business_date_value; isin_code := isin_code_value; denominator_coefficient_of_adjustment := denominator_coefficient_of_adjustment_value; numerator_adjustment_of_coefficient := numerator_adjustment_of_coefficient_value; trading_multiplier_before_adjustment := trading_multiplier_before_adjustment_value; trading_multiplier_after_adjustment_equity_options_10 := trading_multiplier_after_adjustment_equity_options_10_value; exercise_price_before_adjustment := exercise_price_before_adjustment_value; exercise_price_after_adjustment := exercise_price_after_adjustment_value; adjustment_coefficient_of_open_intetest_volumes_that_have_been_adjusted := adjustment_coefficient_of_open_intetest_volumes_that_have_been_adjusted_value; end_keyword := end_keyword_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 151.
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

  End EquityDerivativesAdjustmentDetailsMessage.

  Module CommodityFuturesSettlementReferenceKtbMessage.

    (** Commodity Futures Settlement Reference for KTB. *)
    Record t := {
      message_sequence_number : list byte;
      application_date : list byte;
      underlying_asset_id : list byte;
      ktb_isin : list byte;
      isin_of_base_issue_for_payment : list byte;
      conversion_factor : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (application_date record) = 8 /\
      Datatypes.length (underlying_asset_id record) = 3 /\
      Datatypes.length (ktb_isin record) = 12 /\
      Datatypes.length (isin_of_base_issue_for_payment record) = 12 /\
      Datatypes.length (conversion_factor record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 8 (application_date record) ++
      encode_bytes 3 (underlying_asset_id record) ++
      encode_bytes 12 (ktb_isin record) ++
      encode_bytes 12 (isin_of_base_issue_for_payment record) ++
      encode_bytes 22 (conversion_factor record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (message_sequence_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (application_date_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (underlying_asset_id_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (ktb_isin_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (isin_of_base_issue_for_payment_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (conversion_factor_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| message_sequence_number := message_sequence_number_value; application_date := application_date_value; underlying_asset_id := underlying_asset_id_value; ktb_isin := ktb_isin_value; isin_of_base_issue_for_payment := isin_of_base_issue_for_payment_value; conversion_factor := conversion_factor_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
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

  End CommodityFuturesSettlementReferenceKtbMessage.

  Module DerivativesInvestorActivitiesMessage.

    (** Investor Activities per Derivatives. Aggregated bid/ask volumes and values by investor category per derivatives product. *)
    Record t := {
      date : list byte;
      calculation_time_activities : list byte;
      transaction_status_type_code : list byte;
      product_id : list byte;
      futures_options_type_code : list byte;
      investor_code : list byte;
      bid_trading_volume : list byte;
      ask_trading_volume : list byte;
      bid_trading_value : list byte;
      ask_trading_value : list byte;
      spread_bid_trading_volume : list byte;
      spread_ask_trading_volume : list byte;
      spread_bid_trading_value : list byte;
      spread_ask_trading_value : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (date record) = 8 /\
      Datatypes.length (calculation_time_activities record) = 6 /\
      Datatypes.length (transaction_status_type_code record) = 2 /\
      Datatypes.length (product_id record) = 11 /\
      Datatypes.length (futures_options_type_code record) = 1 /\
      Datatypes.length (investor_code record) = 4 /\
      Datatypes.length (bid_trading_volume record) = 10 /\
      Datatypes.length (ask_trading_volume record) = 10 /\
      Datatypes.length (bid_trading_value record) = 22 /\
      Datatypes.length (ask_trading_value record) = 22 /\
      Datatypes.length (spread_bid_trading_volume record) = 10 /\
      Datatypes.length (spread_ask_trading_volume record) = 10 /\
      Datatypes.length (spread_bid_trading_value record) = 22 /\
      Datatypes.length (spread_ask_trading_value record) = 22 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (date record) ++
      encode_bytes 6 (calculation_time_activities record) ++
      encode_bytes 2 (transaction_status_type_code record) ++
      encode_bytes 11 (product_id record) ++
      encode_bytes 1 (futures_options_type_code record) ++
      encode_bytes 4 (investor_code record) ++
      encode_bytes 10 (bid_trading_volume record) ++
      encode_bytes 10 (ask_trading_volume record) ++
      encode_bytes 22 (bid_trading_value record) ++
      encode_bytes 22 (ask_trading_value record) ++
      encode_bytes 10 (spread_bid_trading_volume record) ++
      encode_bytes 10 (spread_ask_trading_volume record) ++
      encode_bytes 22 (spread_bid_trading_value record) ++
      encode_bytes 22 (spread_ask_trading_value record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (date_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (calculation_time_activities_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (transaction_status_type_code_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (product_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (futures_options_type_code_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (investor_code_value, bytes) =>
                              match decode_bytes 10 bytes with
                              | None => None
                              | Some (bid_trading_volume_value, bytes) =>
                                  match decode_bytes 10 bytes with
                                  | None => None
                                  | Some (ask_trading_volume_value, bytes) =>
                                      match decode_bytes 22 bytes with
                                      | None => None
                                      | Some (bid_trading_value_value, bytes) =>
                                          match decode_bytes 22 bytes with
                                          | None => None
                                          | Some (ask_trading_value_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (spread_bid_trading_volume_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (spread_ask_trading_volume_value, bytes) =>
                                                      match decode_bytes 22 bytes with
                                                      | None => None
                                                      | Some (spread_bid_trading_value_value, bytes) =>
                                                          match decode_bytes 22 bytes with
                                                          | None => None
                                                          | Some (spread_ask_trading_value_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (end_keyword_value, bytes) =>
                                                                  Some ({| date := date_value; calculation_time_activities := calculation_time_activities_value; transaction_status_type_code := transaction_status_type_code_value; product_id := product_id_value; futures_options_type_code := futures_options_type_code_value; investor_code := investor_code_value; bid_trading_volume := bid_trading_volume_value; ask_trading_volume := ask_trading_volume_value; bid_trading_value := bid_trading_value_value; ask_trading_value := ask_trading_value_value; spread_bid_trading_volume := spread_bid_trading_volume_value; spread_ask_trading_volume := spread_ask_trading_volume_value; spread_bid_trading_value := spread_bid_trading_value_value; spread_ask_trading_value := spread_ask_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 161.
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

  End DerivativesInvestorActivitiesMessage.

  Module DerivativesOpenInterestMessage.

    (** Derivatives Open Interest. Total open interest per derivatives contract. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      open_interest_type_code : list byte;
      trading_date : list byte;
      open_interest : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (open_interest_type_code record) = 2 /\
      Datatypes.length (trading_date record) = 8 /\
      Datatypes.length (open_interest record) = 10 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 2 (open_interest_type_code record) ++
      encode_bytes 8 (trading_date record) ++
      encode_bytes 10 (open_interest record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (open_interest_type_code_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (trading_date_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (open_interest_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; open_interest_type_code := open_interest_type_code_value; trading_date := trading_date_value; open_interest := open_interest_value; end_keyword := end_keyword_value |}, bytes)
                          end
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

  End DerivativesOpenInterestMessage.

  Module FuturesSettledPriceMessage.

    (** Futures Settled Price. Daily settled price for futures contracts. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      settlement_price : list byte;
      settlement_price_type_code : list byte;
      the_last_settlement_price : list byte;
      last_settlement_price_type_code : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (settlement_price record) = 18 /\
      Datatypes.length (settlement_price_type_code record) = 2 /\
      Datatypes.length (the_last_settlement_price record) = 18 /\
      Datatypes.length (last_settlement_price_type_code record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 18 (settlement_price record) ++
      encode_bytes 2 (settlement_price_type_code record) ++
      encode_bytes 18 (the_last_settlement_price record) ++
      encode_bytes 1 (last_settlement_price_type_code record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 18 bytes with
              | None => None
              | Some (settlement_price_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (settlement_price_type_code_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (the_last_settlement_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (last_settlement_price_type_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; settlement_price := settlement_price_value; settlement_price_type_code := settlement_price_type_code_value; the_last_settlement_price := the_last_settlement_price_value; last_settlement_price_type_code := last_settlement_price_type_code_value; end_keyword := end_keyword_value |}, bytes)
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

  End FuturesSettledPriceMessage.

  Module OptionsBasePriceOfClearingMarginsMessage.

    (** Options Base Price of Clearing Margins. Base price used for margin calculation. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      base_price_of_clearing_margins : list byte;
      base_price_of_clearing_margins_type_code : list byte;
      settlement_price_after_exercising_an_option : list byte;
      type_code_of_settlement_price_after_exercising_an_option : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (base_price_of_clearing_margins record) = 18 /\
      Datatypes.length (base_price_of_clearing_margins_type_code record) = 2 /\
      Datatypes.length (settlement_price_after_exercising_an_option record) = 18 /\
      Datatypes.length (type_code_of_settlement_price_after_exercising_an_option record) = 1 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 18 (base_price_of_clearing_margins record) ++
      encode_bytes 2 (base_price_of_clearing_margins_type_code record) ++
      encode_bytes 18 (settlement_price_after_exercising_an_option record) ++
      encode_bytes 1 (type_code_of_settlement_price_after_exercising_an_option record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 18 bytes with
              | None => None
              | Some (base_price_of_clearing_margins_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (base_price_of_clearing_margins_type_code_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (settlement_price_after_exercising_an_option_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (type_code_of_settlement_price_after_exercising_an_option_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; base_price_of_clearing_margins := base_price_of_clearing_margins_value; base_price_of_clearing_margins_type_code := base_price_of_clearing_margins_type_code_value; settlement_price_after_exercising_an_option := settlement_price_after_exercising_an_option_value; type_code_of_settlement_price_after_exercising_an_option := type_code_of_settlement_price_after_exercising_an_option_value; end_keyword := end_keyword_value |}, bytes)
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

  End OptionsBasePriceOfClearingMarginsMessage.

  Module OptionsImpliedVolatilityMessage.

    (** Options Implied Volatility per option contract. *)
    Record t := {
      call_averaged_implied_volatility : list byte;
      put_averaged_implied_volatility : list byte;
      representative_implied_volatility : list byte;
      historical_volatility_90_days : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (call_averaged_implied_volatility record) = 11 /\
      Datatypes.length (put_averaged_implied_volatility record) = 11 /\
      Datatypes.length (representative_implied_volatility record) = 11 /\
      Datatypes.length (historical_volatility_90_days record) = 11 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (call_averaged_implied_volatility record) ++
      encode_bytes 11 (put_averaged_implied_volatility record) ++
      encode_bytes 11 (representative_implied_volatility record) ++
      encode_bytes 11 (historical_volatility_90_days record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (call_averaged_implied_volatility_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (put_averaged_implied_volatility_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (representative_implied_volatility_value, bytes) =>
                  match decode_bytes 11 bytes with
                  | None => None
                  | Some (historical_volatility_90_days_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (end_keyword_value, bytes) =>
                          Some ({| call_averaged_implied_volatility := call_averaged_implied_volatility_value; put_averaged_implied_volatility := put_averaged_implied_volatility_value; representative_implied_volatility := representative_implied_volatility_value; historical_volatility_90_days := historical_volatility_90_days_value; end_keyword := end_keyword_value |}, bytes)
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

  End OptionsImpliedVolatilityMessage.

  Module OptionsSensitivityMessage.

    (** Options Sensitivity. Greeks (Delta, Gamma, Theta, Vega, Rho) per option contract. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue : list byte;
      calculating_date : list byte;
      calculation_time_sensitivity : list byte;
      implied_volatility_type_code : list byte;
      underlying_asset_id : list byte;
      sensitivity_delta : list byte;
      sensitivity_theta : list byte;
      sensitivity_vega : list byte;
      sensitivity_gamma : list byte;
      sensitivity_rho : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue record) = 6 /\
      Datatypes.length (calculating_date record) = 8 /\
      Datatypes.length (calculation_time_sensitivity record) = 9 /\
      Datatypes.length (implied_volatility_type_code record) = 1 /\
      Datatypes.length (underlying_asset_id record) = 3 /\
      Datatypes.length (sensitivity_delta record) = 20 /\
      Datatypes.length (sensitivity_theta record) = 20 /\
      Datatypes.length (sensitivity_vega record) = 20 /\
      Datatypes.length (sensitivity_gamma record) = 20 /\
      Datatypes.length (sensitivity_rho record) = 20 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue record) ++
      encode_bytes 8 (calculating_date record) ++
      encode_bytes 9 (calculation_time_sensitivity record) ++
      encode_bytes 1 (implied_volatility_type_code record) ++
      encode_bytes 3 (underlying_asset_id record) ++
      encode_bytes 20 (sensitivity_delta record) ++
      encode_bytes 20 (sensitivity_theta record) ++
      encode_bytes 20 (sensitivity_vega record) ++
      encode_bytes 20 (sensitivity_gamma record) ++
      encode_bytes 20 (sensitivity_rho record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (calculating_date_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (calculation_time_sensitivity_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (implied_volatility_type_code_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (underlying_asset_id_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (sensitivity_delta_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (sensitivity_theta_value, bytes) =>
                                      match decode_bytes 20 bytes with
                                      | None => None
                                      | Some (sensitivity_vega_value, bytes) =>
                                          match decode_bytes 20 bytes with
                                          | None => None
                                          | Some (sensitivity_gamma_value, bytes) =>
                                              match decode_bytes 20 bytes with
                                              | None => None
                                              | Some (sensitivity_rho_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (end_keyword_value, bytes) =>
                                                      Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue := a_designated_number_for_an_issue_value; calculating_date := calculating_date_value; calculation_time_sensitivity := calculation_time_sensitivity_value; implied_volatility_type_code := implied_volatility_type_code_value; underlying_asset_id := underlying_asset_id_value; sensitivity_delta := sensitivity_delta_value; sensitivity_theta := sensitivity_theta_value; sensitivity_vega := sensitivity_vega_value; sensitivity_gamma := sensitivity_gamma_value; sensitivity_rho := sensitivity_rho_value; end_keyword := end_keyword_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 140.
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

  End OptionsSensitivityMessage.

  Module CommodityFuturesSpotSettlementReferenceMessage.

    (** Commodity Futures Spot Market Info Settlement Reference. *)
    Record t := {
      bis_announcement_date : list byte;
      bis_announcement_time : list byte;
      underlying_asset_id : list byte;
      bis_yield_ratio : list byte;
      isin_of_base_issue_for_payment : list byte;
      ktb_isin : list byte;
      bis_time_of_inputting_yield_rate : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bis_announcement_date record) = 8 /\
      Datatypes.length (bis_announcement_time record) = 6 /\
      Datatypes.length (underlying_asset_id record) = 3 /\
      Datatypes.length (bis_yield_ratio record) = 9 /\
      Datatypes.length (isin_of_base_issue_for_payment record) = 12 /\
      Datatypes.length (ktb_isin record) = 12 /\
      Datatypes.length (bis_time_of_inputting_yield_rate record) = 4 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (bis_announcement_date record) ++
      encode_bytes 6 (bis_announcement_time record) ++
      encode_bytes 3 (underlying_asset_id record) ++
      encode_bytes 9 (bis_yield_ratio record) ++
      encode_bytes 12 (isin_of_base_issue_for_payment record) ++
      encode_bytes 12 (ktb_isin record) ++
      encode_bytes 4 (bis_time_of_inputting_yield_rate record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (bis_announcement_date_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (bis_announcement_time_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (underlying_asset_id_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (bis_yield_ratio_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (isin_of_base_issue_for_payment_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (ktb_isin_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (bis_time_of_inputting_yield_rate_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| bis_announcement_date := bis_announcement_date_value; bis_announcement_time := bis_announcement_time_value; underlying_asset_id := underlying_asset_id_value; bis_yield_ratio := bis_yield_ratio_value; isin_of_base_issue_for_payment := isin_of_base_issue_for_payment_value; ktb_isin := ktb_isin_value; bis_time_of_inputting_yield_rate := bis_time_of_inputting_yield_rate_value; end_keyword := end_keyword_value |}, bytes)
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

  End CommodityFuturesSpotSettlementReferenceMessage.

  Module DailyDisclosedRfrMessage.

    (** Daily disclosed Risk-Free Rate (RFR) reference. *)
    Record t := {
      base_date : list byte;
      disclosure_type : list byte;
      disclosure_date : list byte;
      rfr : list byte;
      indexed_interest_rate : list byte;
      interest_rate_30_day : list byte;
      interest_rate_90_day : list byte;
      interest_rate_180_day : list byte;
      end_keyword : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (base_date record) = 8 /\
      Datatypes.length (disclosure_type record) = 2 /\
      Datatypes.length (disclosure_date record) = 14 /\
      Datatypes.length (rfr record) = 9 /\
      Datatypes.length (indexed_interest_rate record) = 12 /\
      Datatypes.length (interest_rate_30_day record) = 12 /\
      Datatypes.length (interest_rate_90_day record) = 12 /\
      Datatypes.length (interest_rate_180_day record) = 12 /\
      (end_keyword record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (base_date record) ++
      encode_bytes 2 (disclosure_type record) ++
      encode_bytes 14 (disclosure_date record) ++
      encode_bytes 9 (rfr record) ++
      encode_bytes 12 (indexed_interest_rate record) ++
      encode_bytes 12 (interest_rate_30_day record) ++
      encode_bytes 12 (interest_rate_90_day record) ++
      encode_bytes 12 (interest_rate_180_day record) ++
      encode_uint 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (base_date_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (disclosure_type_value, bytes) =>
              match decode_bytes 14 bytes with
              | None => None
              | Some (disclosure_date_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (rfr_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (indexed_interest_rate_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (interest_rate_30_day_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (interest_rate_90_day_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (interest_rate_180_day_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (end_keyword_value, bytes) =>
                                          Some ({| base_date := base_date_value; disclosure_type := disclosure_type_value; disclosure_date := disclosure_date_value; rfr := rfr_value; indexed_interest_rate := indexed_interest_rate_value; interest_rate_30_day := interest_rate_30_day_value; interest_rate_90_day := interest_rate_90_day_value; interest_rate_180_day := interest_rate_180_day_value; end_keyword := end_keyword_value |}, bytes)
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

  End DailyDisclosedRfrMessage.

End KoscomMdcsRealtimeDerivativesAV2020.
