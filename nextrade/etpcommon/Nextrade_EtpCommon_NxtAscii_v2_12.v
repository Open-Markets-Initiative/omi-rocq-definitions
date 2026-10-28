From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Nextrade Nextrade Etp Market Data Common

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

Module NextradeEtpCommonV212.

  Module PollingDataMessage.

    (** The data is provided periodically in order to check multicast group status. *)
    Record t := {
      current_time_1_minute_interval : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (current_time_1_minute_interval record) = 4 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (current_time_1_minute_interval record) ++
      encode_bytes 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (current_time_1_minute_interval_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (end_keyword_value, bytes) =>
              Some ({| current_time_1_minute_interval := current_time_1_minute_interval_value; end_keyword := end_keyword_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End PollingDataMessage.

  Module SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.

    (** Securities_Quote (MM/LP Quotes Included, 10 Level) Best Order Data on NXT Trading Items provided - MM/LP Quotes Included * 10 Level Best Order on Ask/Bid. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
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
      mid_price : list byte;
      total_mid_price_ask_volume_total_ask_volume_on_mid_price : list byte;
      total_mid_price_bid_volume_total_bid_volume_on_mid_price : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
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
      Datatypes.length (mid_price record) = 11 /\
      Datatypes.length (total_mid_price_ask_volume_total_ask_volume_on_mid_price record) = 12 /\
      Datatypes.length (total_mid_price_bid_volume_total_bid_volume_on_mid_price record) = 12 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
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
      encode_bytes 11 (mid_price record) ++
      encode_bytes 12 (total_mid_price_ask_volume_total_ask_volume_on_mid_price record) ++
      encode_bytes 12 (total_mid_price_bid_volume_total_bid_volume_on_mid_price record) ++
      encode_bytes 1 (end_keyword record).

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
                      | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
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
                                                                                                                                                                                                                                                                                              | Some (mid_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (total_mid_price_ask_volume_total_ask_volume_on_mid_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (total_mid_price_bid_volume_total_bid_volume_on_mid_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                          | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                              Some ({| message_sequence_number := message_sequence_number_value; board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; processing_time_of_trading_system := processing_time_of_trading_system_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; lp_ask_level_1_volume := lp_ask_level_1_volume_value; lp_bid_level_1_volume := lp_bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; lp_ask_level_2_volume := lp_ask_level_2_volume_value; lp_bid_level_2_volume := lp_bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; lp_ask_level_3_volume := lp_ask_level_3_volume_value; lp_bid_level_3_volume := lp_bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; lp_ask_level_4_volume := lp_ask_level_4_volume_value; lp_bid_level_4_volume := lp_bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; lp_ask_level_5_volume := lp_ask_level_5_volume_value; lp_bid_level_5_volume := lp_bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; lp_ask_level_6_volume := lp_ask_level_6_volume_value; lp_bid_level_6_volume := lp_bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; lp_ask_level_7_volume := lp_ask_level_7_volume_value; lp_bid_level_7_volume := lp_bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; lp_ask_level_8_volume := lp_ask_level_8_volume_value; lp_bid_level_8_volume := lp_bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; lp_ask_level_9_volume := lp_ask_level_9_volume_value; lp_bid_level_9_volume := lp_bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; lp_ask_level_10_volume := lp_ask_level_10_volume_value; lp_bid_level_10_volume := lp_bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; mid_price := mid_price_value; total_mid_price_ask_volume_total_ask_volume_on_mid_price := total_mid_price_ask_volume_total_ask_volume_on_mid_price_value; total_mid_price_bid_volume_total_bid_volume_on_mid_price := total_mid_price_bid_volume_total_bid_volume_on_mid_price_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_73.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesQuoteMmLpQuotesIncluded10LevelMessage.

  Module SecuritiesOrderFilledMessage.

    (** Securities_Order Filled Order Filled Data on NXT trading items provided. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
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
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
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
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
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
      encode_bytes 1 (end_keyword record).

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
                      | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
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
                                                                                  match decode_bytes 1 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 181.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecuritiesOrderFilledMessage.

  Module MarketOperationTsMessage.

    (** The data is provided per an issue if a Market Operation Trading session event occurs. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
      processing_time_of_trading_system : list byte;
      board_event_id : list byte;
      start_time_of_a_board_event : list byte;
      board_event_group_code : list byte;
      trading_halt_reason_code : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (board_event_id record) = 3 /\
      Datatypes.length (start_time_of_a_board_event record) = 9 /\
      Datatypes.length (board_event_group_code record) = 5 /\
      Datatypes.length (trading_halt_reason_code record) = 3 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 3 (board_event_id record) ++
      encode_bytes 9 (start_time_of_a_board_event record) ++
      encode_bytes 5 (board_event_group_code record) ++
      encode_bytes 3 (trading_halt_reason_code record) ++
      encode_bytes 1 (end_keyword record).

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
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (board_event_group_code_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (trading_halt_reason_code_value, bytes) =>
                                              match decode_bytes 1 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketOperationTsMessage.

  Module IssueClosingMessage.

    (** The data is provided in case of an issue closing per board. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
      closing_price : list byte;
      closing_price_type_code : list byte;
      upper_limit_price_on_the_single_price_trade_in_the_off_hours_session : list byte;
      lower_limit_price_on_the_single_price_trade_in_the_off_hours_session : list byte;
      closing_price_weighted_stock_price_average : list byte;
      closing_price_base_price_of_buy_in : list byte;
      closing_price_upper_limit_of_buy_in : list byte;
      closing_price_lower_limit_of_buy_in : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
      Datatypes.length (closing_price record) = 11 /\
      Datatypes.length (closing_price_type_code record) = 1 /\
      Datatypes.length (upper_limit_price_on_the_single_price_trade_in_the_off_hours_session record) = 11 /\
      Datatypes.length (lower_limit_price_on_the_single_price_trade_in_the_off_hours_session record) = 11 /\
      Datatypes.length (closing_price_weighted_stock_price_average record) = 11 /\
      Datatypes.length (closing_price_base_price_of_buy_in record) = 11 /\
      Datatypes.length (closing_price_upper_limit_of_buy_in record) = 11 /\
      Datatypes.length (closing_price_lower_limit_of_buy_in record) = 11 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 11 (closing_price record) ++
      encode_bytes 1 (closing_price_type_code record) ++
      encode_bytes 11 (upper_limit_price_on_the_single_price_trade_in_the_off_hours_session record) ++
      encode_bytes 11 (lower_limit_price_on_the_single_price_trade_in_the_off_hours_session record) ++
      encode_bytes 11 (closing_price_weighted_stock_price_average record) ++
      encode_bytes 11 (closing_price_base_price_of_buy_in record) ++
      encode_bytes 11 (closing_price_upper_limit_of_buy_in record) ++
      encode_bytes 11 (closing_price_lower_limit_of_buy_in record) ++
      encode_bytes 1 (end_keyword record).

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
                  | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                      match decode_bytes 11 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (closing_price_type_code_value, bytes) =>
                              match decode_bytes 11 bytes with
                              | None => None
                              | Some (upper_limit_price_on_the_single_price_trade_in_the_off_hours_session_value, bytes) =>
                                  match decode_bytes 11 bytes with
                                  | None => None
                                  | Some (lower_limit_price_on_the_single_price_trade_in_the_off_hours_session_value, bytes) =>
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
                                                      match decode_bytes 1 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 107.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IssueClosingMessage.

  Module TriggeringRemovingViMessage.

    (** Triggering/removing VI (Volatility Interruption). *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
      processing_time_of_trading_system : list byte;
      the_time_ending_vi : list byte;
      vi_status_code : list byte;
      vi_type_code : list byte;
      a_base_price_to_trigger_static_vi : list byte;
      a_base_price_to_trigger_dynamic_vi : list byte;
      vi_triggering_price : list byte;
      disparate_ratio_to_trigger_static_vi : list byte;
      disparate_ratio_to_trigger_dynamic_vi : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
      Datatypes.length (processing_time_of_trading_system record) = 12 /\
      Datatypes.length (the_time_ending_vi record) = 9 /\
      Datatypes.length (vi_status_code record) = 1 /\
      Datatypes.length (vi_type_code record) = 1 /\
      Datatypes.length (a_base_price_to_trigger_static_vi record) = 11 /\
      Datatypes.length (a_base_price_to_trigger_dynamic_vi record) = 11 /\
      Datatypes.length (vi_triggering_price record) = 11 /\
      Datatypes.length (disparate_ratio_to_trigger_static_vi record) = 13 /\
      Datatypes.length (disparate_ratio_to_trigger_dynamic_vi record) = 13 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (processing_time_of_trading_system record) ++
      encode_bytes 9 (the_time_ending_vi record) ++
      encode_bytes 1 (vi_status_code record) ++
      encode_bytes 1 (vi_type_code record) ++
      encode_bytes 11 (a_base_price_to_trigger_static_vi record) ++
      encode_bytes 11 (a_base_price_to_trigger_dynamic_vi record) ++
      encode_bytes 11 (vi_triggering_price record) ++
      encode_bytes 13 (disparate_ratio_to_trigger_static_vi record) ++
      encode_bytes 13 (disparate_ratio_to_trigger_dynamic_vi record) ++
      encode_bytes 1 (end_keyword record).

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
                                                          match decode_bytes 1 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 111.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TriggeringRemovingViMessage.

  Module ClosingPriceTradingQuoteMessage.

    (** Total Ask/Bid volume per Issue on Closing Price Trade. *)
    Record t := {
      message_sequence_number : list byte;
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
      total_ask_volume : list byte;
      total_bid_volume : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
      Datatypes.length (total_ask_volume record) = 12 /\
      Datatypes.length (total_bid_volume record) = 12 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (total_ask_volume record) ++
      encode_bytes 12 (total_bid_volume record) ++
      encode_bytes 1 (end_keyword record).

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
                  | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (total_ask_volume_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (total_bid_volume_value, bytes) =>
                              match decode_bytes 1 bytes with
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
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

  End ClosingPriceTradingQuoteMessage.

  Module EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.

    (** Snapshot and final status are provided with certain intervals per issue and board - MM/LP Quotes Included * 10 Level Best Order on Ask/Bid. *)
    Record t := {
      board_id : list byte;
      session_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
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
      mid_price : list byte;
      total_mid_price_ask_volume_total_ask_volume_on_mid_price : list byte;
      total_mid_price_bid_volume_total_bid_volume_on_mid_price : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (session_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
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
      Datatypes.length (mid_price record) = 11 /\
      Datatypes.length (total_mid_price_ask_volume_total_ask_volume_on_mid_price record) = 12 /\
      Datatypes.length (total_mid_price_bid_volume_total_bid_volume_on_mid_price record) = 12 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 2 (session_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
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
      encode_bytes 11 (mid_price record) ++
      encode_bytes 12 (total_mid_price_ask_volume_total_ask_volume_on_mid_price record) ++
      encode_bytes 12 (total_mid_price_bid_volume_total_bid_volume_on_mid_price record) ++
      encode_bytes 1 (end_keyword record).

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
                  | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
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
                                                                                                                                                                                                                                                                                                                                                  | Some (mid_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                      | Some (total_mid_price_ask_volume_total_ask_volume_on_mid_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 12 bytes with
                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                          | Some (total_mid_price_bid_volume_total_bid_volume_on_mid_price_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                              | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                  Some ({| board_id := board_id_value; session_id := session_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; price_change_against_previous_day := price_change_against_previous_day_value; a_price_change_against_the_previous_day := a_price_change_against_the_previous_day_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; current_price := current_price_value; opening_price := opening_price_value; todays_high := todays_high_value; todays_low := todays_low_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; final_ask_bid_type_code := final_ask_bid_type_code_value; ask_level_1_price := ask_level_1_price_value; bid_level_1_price := bid_level_1_price_value; ask_level_1_volume := ask_level_1_volume_value; bid_level_1_volume := bid_level_1_volume_value; lp_ask_level_1_volume := lp_ask_level_1_volume_value; lp_bid_level_1_volume := lp_bid_level_1_volume_value; ask_level_2_price := ask_level_2_price_value; bid_level_2_price := bid_level_2_price_value; ask_level_2_volume := ask_level_2_volume_value; bid_level_2_volume := bid_level_2_volume_value; lp_ask_level_2_volume := lp_ask_level_2_volume_value; lp_bid_level_2_volume := lp_bid_level_2_volume_value; ask_level_3_price := ask_level_3_price_value; bid_level_3_price := bid_level_3_price_value; ask_level_3_volume := ask_level_3_volume_value; bid_level_3_volume := bid_level_3_volume_value; lp_ask_level_3_volume := lp_ask_level_3_volume_value; lp_bid_level_3_volume := lp_bid_level_3_volume_value; ask_level_4_price := ask_level_4_price_value; bid_level_4_price := bid_level_4_price_value; ask_level_4_volume := ask_level_4_volume_value; bid_level_4_volume := bid_level_4_volume_value; lp_ask_level_4_volume := lp_ask_level_4_volume_value; lp_bid_level_4_volume := lp_bid_level_4_volume_value; ask_level_5_price := ask_level_5_price_value; bid_level_5_price := bid_level_5_price_value; ask_level_5_volume := ask_level_5_volume_value; bid_level_5_volume := bid_level_5_volume_value; lp_ask_level_5_volume := lp_ask_level_5_volume_value; lp_bid_level_5_volume := lp_bid_level_5_volume_value; ask_level_6_price := ask_level_6_price_value; bid_level_6_price := bid_level_6_price_value; ask_level_6_volume := ask_level_6_volume_value; bid_level_6_volume := bid_level_6_volume_value; lp_ask_level_6_volume := lp_ask_level_6_volume_value; lp_bid_level_6_volume := lp_bid_level_6_volume_value; ask_level_7_price := ask_level_7_price_value; bid_level_7_price := bid_level_7_price_value; ask_level_7_volume := ask_level_7_volume_value; bid_level_7_volume := bid_level_7_volume_value; lp_ask_level_7_volume := lp_ask_level_7_volume_value; lp_bid_level_7_volume := lp_bid_level_7_volume_value; ask_level_8_price := ask_level_8_price_value; bid_level_8_price := bid_level_8_price_value; ask_level_8_volume := ask_level_8_volume_value; bid_level_8_volume := bid_level_8_volume_value; lp_ask_level_8_volume := lp_ask_level_8_volume_value; lp_bid_level_8_volume := lp_bid_level_8_volume_value; ask_level_9_price := ask_level_9_price_value; bid_level_9_price := bid_level_9_price_value; ask_level_9_volume := ask_level_9_volume_value; bid_level_9_volume := bid_level_9_volume_value; lp_ask_level_9_volume := lp_ask_level_9_volume_value; lp_bid_level_9_volume := lp_bid_level_9_volume_value; ask_level_10_price := ask_level_10_price_value; bid_level_10_price := bid_level_10_price_value; ask_level_10_volume := ask_level_10_volume_value; bid_level_10_volume := bid_level_10_volume_value; lp_ask_level_10_volume := lp_ask_level_10_volume_value; lp_bid_level_10_volume := lp_bid_level_10_volume_value; total_ask_volume := total_ask_volume_value; total_bid_volume := total_bid_volume_value; estimated_trading_price := estimated_trading_price_value; estimated_trading_volume := estimated_trading_volume_value; closing_price_type_code := closing_price_type_code_value; trading_halt := trading_halt_value; knock_out_elw_type_code := knock_out_elw_type_code_value; knock_out_elw_triggering_time := knock_out_elw_triggering_time_value; mid_price := mid_price_value; total_mid_price_ask_volume_total_ask_volume_on_mid_price := total_mid_price_ask_volume_total_ask_volume_on_mid_price_value; total_mid_price_bid_volume_total_bid_volume_on_mid_price := total_mid_price_bid_volume_total_bid_volume_on_mid_price_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_86.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EquitiesSnapshotMmLpQuotesIncluded10LevelMessage.

  Module InvestorActivitiesPerCommoditiesMessage.

    (** Investor Activities per Commodities. *)
    Record t := {
      calculation_time : list byte;
      investor_code : list byte;
      accumulated_ask_trading_volume : list byte;
      accumulated_ask_trading_value : list byte;
      accumulated_bid_trading_volume : list byte;
      accumulated_bid_trading_value : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (calculation_time record) = 6 /\
      Datatypes.length (investor_code record) = 4 /\
      Datatypes.length (accumulated_ask_trading_volume record) = 12 /\
      Datatypes.length (accumulated_ask_trading_value record) = 22 /\
      Datatypes.length (accumulated_bid_trading_volume record) = 12 /\
      Datatypes.length (accumulated_bid_trading_value record) = 22 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (calculation_time record) ++
      encode_bytes 4 (investor_code record) ++
      encode_bytes 12 (accumulated_ask_trading_volume record) ++
      encode_bytes 22 (accumulated_ask_trading_value record) ++
      encode_bytes 12 (accumulated_bid_trading_volume record) ++
      encode_bytes 22 (accumulated_bid_trading_value record) ++
      encode_bytes 1 (end_keyword record).

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
                              match decode_bytes 1 bytes with
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

  End InvestorActivitiesPerCommoditiesMessage.

  Module EtpConstituentsMessage.

    (** Constituents of Structured Products. *)
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
      end_keyword : list byte;
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
      Datatypes.length (end_keyword record) = 1.

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
      encode_bytes 1 (end_keyword record).

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
                                                  match decode_bytes 1 bytes with
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EtpConstituentsMessage.

  Module MmLpInformationMessage.

    (** Details. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      market_participant_number : list byte;
      board_id : list byte;
      market_making_lp_type_code : list byte;
      lp_start_date : list byte;
      lp_end_date : list byte;
      minimum_order_volume : list byte;
      maximum_volume_of_multiple_order : list byte;
      bid_ask_spread_unit_code : list byte;
      main_market_bid_ask_spread_value : list byte;
      spread_multiple_for_market_holidays : list byte;
      an_obligatory_time_interval_to_place_an_order : list byte;
      minimum_ask_price : list byte;
      maximum_bid_price : list byte;
      minimum_order_price : list byte;
      maximum_order_price : list byte;
      extended_market_bid_ask_spread_value : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (market_participant_number record) = 5 /\
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (market_making_lp_type_code record) = 1 /\
      Datatypes.length (lp_start_date record) = 8 /\
      Datatypes.length (lp_end_date record) = 8 /\
      Datatypes.length (minimum_order_volume record) = 11 /\
      Datatypes.length (maximum_volume_of_multiple_order record) = 11 /\
      Datatypes.length (bid_ask_spread_unit_code record) = 1 /\
      Datatypes.length (main_market_bid_ask_spread_value record) = 22 /\
      Datatypes.length (spread_multiple_for_market_holidays record) = 11 /\
      Datatypes.length (an_obligatory_time_interval_to_place_an_order record) = 6 /\
      Datatypes.length (minimum_ask_price record) = 22 /\
      Datatypes.length (maximum_bid_price record) = 22 /\
      Datatypes.length (minimum_order_price record) = 22 /\
      Datatypes.length (maximum_order_price record) = 22 /\
      Datatypes.length (extended_market_bid_ask_spread_value record) = 22 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 5 (market_participant_number record) ++
      encode_bytes 2 (board_id record) ++
      encode_bytes 1 (market_making_lp_type_code record) ++
      encode_bytes 8 (lp_start_date record) ++
      encode_bytes 8 (lp_end_date record) ++
      encode_bytes 11 (minimum_order_volume record) ++
      encode_bytes 11 (maximum_volume_of_multiple_order record) ++
      encode_bytes 1 (bid_ask_spread_unit_code record) ++
      encode_bytes 22 (main_market_bid_ask_spread_value record) ++
      encode_bytes 11 (spread_multiple_for_market_holidays record) ++
      encode_bytes 6 (an_obligatory_time_interval_to_place_an_order record) ++
      encode_bytes 22 (minimum_ask_price record) ++
      encode_bytes 22 (maximum_bid_price record) ++
      encode_bytes 22 (minimum_order_price record) ++
      encode_bytes 22 (maximum_order_price record) ++
      encode_bytes 22 (extended_market_bid_ask_spread_value record) ++
      encode_bytes 1 (end_keyword record).

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
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (board_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (market_making_lp_type_code_value, bytes) =>
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
                                              | Some (main_market_bid_ask_spread_value_value, bytes) =>
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
                                                                          match decode_bytes 22 bytes with
                                                                          | None => None
                                                                          | Some (extended_market_bid_ask_spread_value_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (end_keyword_value, bytes) =>
                                                                                  Some ({| message_sequence_number := message_sequence_number_value; isin_code := isin_code_value; market_participant_number := market_participant_number_value; board_id := board_id_value; market_making_lp_type_code := market_making_lp_type_code_value; lp_start_date := lp_start_date_value; lp_end_date := lp_end_date_value; minimum_order_volume := minimum_order_volume_value; maximum_volume_of_multiple_order := maximum_volume_of_multiple_order_value; bid_ask_spread_unit_code := bid_ask_spread_unit_code_value; main_market_bid_ask_spread_value := main_market_bid_ask_spread_value_value; spread_multiple_for_market_holidays := spread_multiple_for_market_holidays_value; an_obligatory_time_interval_to_place_an_order := an_obligatory_time_interval_to_place_an_order_value; minimum_ask_price := minimum_ask_price_value; maximum_bid_price := maximum_bid_price_value; minimum_order_price := minimum_order_price_value; maximum_order_price := maximum_order_price_value; extended_market_bid_ask_spread_value := extended_market_bid_ask_spread_value_value; end_keyword := end_keyword_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 217.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MmLpInformationMessage.

  Module MarketOperationScheduleMessage.

    (** The data is provided when a Market Operation Schedule event is disclosed. *)
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
      end_keyword : list byte;
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
      Datatypes.length (end_keyword record) = 1.

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
      encode_bytes 1 (end_keyword record).

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
                                                                  match decode_bytes 1 bytes with
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketOperationScheduleMessage.

  Module MemberFirmImposingLiftingSanctionsMessage.

    (** The data is provided when a sanction is imposed on a member firm or lifted. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
      disclosing_data_type_code : list byte;
      disclosure_time : list byte;
      member_number : list byte;
      member_firm_trust_principal_type_code : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
      Datatypes.length (disclosing_data_type_code record) = 3 /\
      Datatypes.length (disclosure_time record) = 9 /\
      Datatypes.length (member_number record) = 5 /\
      Datatypes.length (member_firm_trust_principal_type_code record) = 5 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 3 (disclosing_data_type_code record) ++
      encode_bytes 9 (disclosure_time record) ++
      encode_bytes 5 (member_number record) ++
      encode_bytes 5 (member_firm_trust_principal_type_code record) ++
      encode_bytes 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
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
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; disclosing_data_type_code := disclosing_data_type_code_value; disclosure_time := disclosure_time_value; member_number := member_number_value; member_firm_trust_principal_type_code := member_firm_trust_principal_type_code_value; end_keyword := end_keyword_value |}, bytes)
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

  End MemberFirmImposingLiftingSanctionsMessage.

  Module TopFiveTradersActivitiesMessage.

    (** Top Five Traders' Activities (including only Regular Board). *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
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
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
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
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
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
      encode_bytes 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
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
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (end_keyword_value, bytes) =>
                                                                                                                                          Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; member_number_1_for_ask := member_number_1_for_ask_value; ask_trading_volume_1 := ask_trading_volume_1_value; ask_trading_value_1 := ask_trading_value_1_value; member_number_1_for_bid := member_number_1_for_bid_value; bid_trading_volume_1 := bid_trading_volume_1_value; bid_trading_value_1 := bid_trading_value_1_value; member_number_2_for_ask := member_number_2_for_ask_value; ask_trading_volume_2 := ask_trading_volume_2_value; ask_trading_value_2 := ask_trading_value_2_value; member_number_2_for_bid := member_number_2_for_bid_value; bid_trading_volume_2 := bid_trading_volume_2_value; bid_trading_value_2 := bid_trading_value_2_value; member_number_3_for_ask := member_number_3_for_ask_value; ask_trading_volume_3 := ask_trading_volume_3_value; ask_trading_value_3 := ask_trading_value_3_value; member_number_3_for_bid := member_number_3_for_bid_value; bid_trading_volume_3 := bid_trading_volume_3_value; bid_trading_value_3 := bid_trading_value_3_value; member_number_4_for_ask := member_number_4_for_ask_value; ask_trading_volume_4 := ask_trading_volume_4_value; ask_trading_value_4 := ask_trading_value_4_value; member_number_4_for_bid := member_number_4_for_bid_value; bid_trading_volume_4 := bid_trading_volume_4_value; bid_trading_value_4 := bid_trading_value_4_value; member_number_5_for_ask := member_number_5_for_ask_value; ask_trading_volume_5 := ask_trading_volume_5_value; ask_trading_value_5 := ask_trading_value_5_value; member_number_5_for_bid := member_number_5_for_bid_value; bid_trading_volume_5 := bid_trading_volume_5_value; bid_trading_value_5 := bid_trading_value_5_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TopFiveTradersActivitiesMessage.

  Module EquitiesBatchDataMessage.

    (** Details. *)
    Record t := {
      message_sequence_number : list byte;
      total_number_of_instruments_of_the_contract : list byte;
      business_date : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
      abbreviated_issue_code : list byte;
      abbreviated_issue_name : list byte;
      abbreviated_issue_name_in_en : list byte;
      group_number : list byte;
      market_operation_product_id : list byte;
      security_group_id : list byte;
      unit_trading : list byte;
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
      yesterdays_closing_price_type_code_krx : list byte;
      yesterdays_closing_price_krx : list byte;
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
      credit_order_possibility : list byte;
      limit_order_permission_type_code : list byte;
      market_price_order_permission_type_code : list byte;
      conditioned_order_permission_type_code : list byte;
      best_favorable_order_permission_type_code : list byte;
      first_best_order_permission_type : list byte;
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
      choice_on_competitive_trading : list byte;
      limit_on_competitive_trading_volume : list byte;
      occurrence_of_reasons_prohibiting_competitive_trading : list byte;
      approval_on_competitive_trading : list byte;
      approval_on_negotiation_trading : list byte;
      yesterdays_closing_price_type_code_nxt : list byte;
      yesterdays_closing_price_nxt : list byte;
      competition_board_trade_permission_code : list byte;
      negotiation_possible_or_not_before_main_market : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (total_number_of_instruments_of_the_contract record) = 6 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
      Datatypes.length (abbreviated_issue_code record) = 9 /\
      Datatypes.length (abbreviated_issue_name record) = 40 /\
      Datatypes.length (abbreviated_issue_name_in_en record) = 40 /\
      Datatypes.length (group_number record) = 5 /\
      Datatypes.length (market_operation_product_id record) = 3 /\
      Datatypes.length (security_group_id record) = 2 /\
      Datatypes.length (unit_trading record) = 1 /\
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
      Datatypes.length (yesterdays_closing_price_type_code_krx record) = 1 /\
      Datatypes.length (yesterdays_closing_price_krx record) = 11 /\
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
      Datatypes.length (credit_order_possibility record) = 1 /\
      Datatypes.length (limit_order_permission_type_code record) = 5 /\
      Datatypes.length (market_price_order_permission_type_code record) = 5 /\
      Datatypes.length (conditioned_order_permission_type_code record) = 5 /\
      Datatypes.length (best_favorable_order_permission_type_code record) = 5 /\
      Datatypes.length (first_best_order_permission_type record) = 5 /\
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
      Datatypes.length (choice_on_competitive_trading record) = 1 /\
      Datatypes.length (limit_on_competitive_trading_volume record) = 1 /\
      Datatypes.length (occurrence_of_reasons_prohibiting_competitive_trading record) = 1 /\
      Datatypes.length (approval_on_competitive_trading record) = 1 /\
      Datatypes.length (approval_on_negotiation_trading record) = 1 /\
      Datatypes.length (yesterdays_closing_price_type_code_nxt record) = 1 /\
      Datatypes.length (yesterdays_closing_price_nxt record) = 11 /\
      Datatypes.length (competition_board_trade_permission_code record) = 5 /\
      Datatypes.length (negotiation_possible_or_not_before_main_market record) = 1 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 6 (total_number_of_instruments_of_the_contract record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 9 (abbreviated_issue_code record) ++
      encode_bytes 40 (abbreviated_issue_name record) ++
      encode_bytes 40 (abbreviated_issue_name_in_en record) ++
      encode_bytes 5 (group_number record) ++
      encode_bytes 3 (market_operation_product_id record) ++
      encode_bytes 2 (security_group_id record) ++
      encode_bytes 1 (unit_trading record) ++
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
      encode_bytes 1 (yesterdays_closing_price_type_code_krx record) ++
      encode_bytes 11 (yesterdays_closing_price_krx record) ++
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
      encode_bytes 1 (credit_order_possibility record) ++
      encode_bytes 5 (limit_order_permission_type_code record) ++
      encode_bytes 5 (market_price_order_permission_type_code record) ++
      encode_bytes 5 (conditioned_order_permission_type_code record) ++
      encode_bytes 5 (best_favorable_order_permission_type_code record) ++
      encode_bytes 5 (first_best_order_permission_type record) ++
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
      encode_bytes 1 (choice_on_competitive_trading record) ++
      encode_bytes 1 (limit_on_competitive_trading_volume record) ++
      encode_bytes 1 (occurrence_of_reasons_prohibiting_competitive_trading record) ++
      encode_bytes 1 (approval_on_competitive_trading record) ++
      encode_bytes 1 (approval_on_negotiation_trading record) ++
      encode_bytes 1 (yesterdays_closing_price_type_code_nxt record) ++
      encode_bytes 11 (yesterdays_closing_price_nxt record) ++
      encode_bytes 5 (competition_board_trade_permission_code record) ++
      encode_bytes 1 (negotiation_possible_or_not_before_main_market record) ++
      encode_bytes 1 (end_keyword record).

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
                      | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
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
                                                  | Some (unit_trading_value, bytes) =>
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
                                                                                                                              | Some (yesterdays_closing_price_type_code_krx_value, bytes) =>
                                                                                                                                  match decode_bytes 11 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (yesterdays_closing_price_krx_value, bytes) =>
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
                                                                                                                                                                                                      | Some (credit_order_possibility_value, bytes) =>
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
                                                                                                                                                                                                                          | Some (first_best_order_permission_type_value, bytes) =>
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
                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (choice_on_competitive_trading_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (limit_on_competitive_trading_volume_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (occurrence_of_reasons_prohibiting_competitive_trading_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (approval_on_competitive_trading_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (approval_on_negotiation_trading_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (yesterdays_closing_price_type_code_nxt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      match decode_bytes 11 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      | Some (yesterdays_closing_price_nxt_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          match decode_bytes 5 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          | Some (competition_board_trade_permission_code_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              | Some (negotiation_possible_or_not_before_main_market_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  | Some (end_keyword_value, bytes) =>
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                      Some ({| message_sequence_number := message_sequence_number_value; total_number_of_instruments_of_the_contract := total_number_of_instruments_of_the_contract_value; business_date := business_date_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; abbreviated_issue_code := abbreviated_issue_code_value; abbreviated_issue_name := abbreviated_issue_name_value; abbreviated_issue_name_in_en := abbreviated_issue_name_in_en_value; group_number := group_number_value; market_operation_product_id := market_operation_product_id_value; security_group_id := security_group_id_value; unit_trading := unit_trading_value; rights_type_code := rights_type_code_value; par_value_type_code := par_value_type_code_value; an_issue_of_which_base_price_is_settled_with_a_todays_single_price := an_issue_of_which_base_price_is_settled_with_a_todays_single_price_value; reevaluation_reason_code := reevaluation_reason_code_value; base_price_change := base_price_change_value; random_end_trigger_code := random_end_trigger_code_value; market_alert := market_alert_value; market_alert_type_code := market_alert_type_code_value; korea_corporate_governance_stock_price_index_kogi := korea_corporate_governance_stock_price_index_kogi_value; issue_for_administration := issue_for_administration_value; unfaithful_disclosure := unfaithful_disclosure_value; back_door_listing := back_door_listing_value; trading_halt := trading_halt_value; industry_id := industry_id_value; small_medium_sized_business := small_medium_sized_business_value; section_type_code := section_type_code_value; investment_institution_type_code := investment_institution_type_code_value; base_price := base_price_value; yesterdays_closing_price_type_code_krx := yesterdays_closing_price_type_code_krx_value; yesterdays_closing_price_krx := yesterdays_closing_price_krx_value; yesterdays_accumulated_trading_amount := yesterdays_accumulated_trading_amount_value; yesterdays_accumulated_trading_value := yesterdays_accumulated_trading_value_value; upper_limit_price := upper_limit_price_value; lower_limit_price := lower_limit_price_value; substitute_price_of_securities := substitute_price_of_securities_value; par_value := par_value_value; issuing_price := issuing_price_value; listing_date := listing_date_value; number_of_listed_shares := number_of_listed_shares_value; liquidation_trade := liquidation_trade_value; the_establishment_date := the_establishment_date_value; maturity_date := maturity_date_value; exercising_period := exercising_period_value; expiration_date_for_right := expiration_date_for_right_value; exercise_price_of_elw_or_bw := exercise_price_of_elw_or_bw_value; capital := capital_value; credit_order_possibility := credit_order_possibility_value; limit_order_permission_type_code := limit_order_permission_type_code_value; market_price_order_permission_type_code := market_price_order_permission_type_code_value; conditioned_order_permission_type_code := conditioned_order_permission_type_code_value; best_favorable_order_permission_type_code := best_favorable_order_permission_type_code_value; first_best_order_permission_type := first_best_order_permission_type_value; mid_price_order_permission_type_code := mid_price_order_permission_type_code_value; stop_limit_price_order_permission_type_code := stop_limit_price_order_permission_type_code_value; capital_increase_type_code := capital_increase_type_code_value; other_stock_type_code := other_stock_type_code_value; national_stock := national_stock_value; appraised_price := appraised_price_value; lowest_order_price := lowest_order_price_value; highest_order_price := highest_order_price_value; unit_of_volume_in_main_board := unit_of_volume_in_main_board_value; lot_size_after_hours_trading := lot_size_after_hours_trading_value; rei_ts_type_code := rei_ts_type_code_value; target_stock_isin_code := target_stock_isin_code_value; currency_iso_code := currency_iso_code_value; country_code := country_code_value; market_making_possibility := market_making_possibility_value; closing_price_trading_possibility_in_the_after_hours := closing_price_trading_possibility_in_the_after_hours_value; closing_price_trading_in_the_pre_opening_market := closing_price_trading_in_the_pre_opening_market_value; block_trading_in_the_pre_opening_market := block_trading_in_the_pre_opening_market_value; basket_trading_in_the_pre_opening_market := basket_trading_in_the_pre_opening_market_value; announcement_of_estimated_trading_price := announcement_of_estimated_trading_price_value; short_selling := short_selling_value; etf_tracking_difference := etf_tracking_difference_value; regs := regs_value; spac := spac_value; tax_type_code := tax_type_code_value; appraisal_ratio_of_substitute_price := appraisal_ratio_of_substitute_price_value; investment_caution_issue := investment_caution_issue_value; delisting_date := delisting_date_value; short_term_overheat_issue_type_code := short_term_overheat_issue_type_code_value; etf_replication_methods_type_code := etf_replication_methods_type_code_value; expiration_date := expiration_date_value; distribution_type_code := distribution_type_code_value; calculation_of_redemption_price_start_date := calculation_of_redemption_price_start_date_value; calculation_of_redemption_price_end_date := calculation_of_redemption_price_end_date_value; etp_product_type_code := etp_product_type_code_value; index_calculation_institution_type_code := index_calculation_institution_type_code_value; index_market_classification_id := index_market_classification_id_value; index_sequence_number := index_sequence_number_value; tracking_index_leverage_inverse_type_code := tracking_index_leverage_inverse_type_code_value; reference_index_leverage_inverse_type_code := reference_index_leverage_inverse_type_code_value; index_asset_classification_id_1 := index_asset_classification_id_1_value; index_asset_classification_id_2 := index_asset_classification_id_2_value; ipo_underwriter_member_number := ipo_underwriter_member_number_value; lp_order := lp_order_value; low_liquidity := low_liquidity_value; abnormal_rise := abnormal_rise_value; upper_limit_quantity := upper_limit_quantity_value; investment_precaution_issue := investment_precaution_issue_value; preferred_stocks_with_lesser_shares := preferred_stocks_with_lesser_shares_value; spac_merger := spac_merger_value; segment_type_code := segment_type_code_value; after_market_possibility := after_market_possibility_value; choice_on_competitive_trading := choice_on_competitive_trading_value; limit_on_competitive_trading_volume := limit_on_competitive_trading_volume_value; occurrence_of_reasons_prohibiting_competitive_trading := occurrence_of_reasons_prohibiting_competitive_trading_value; approval_on_competitive_trading := approval_on_competitive_trading_value; approval_on_negotiation_trading := approval_on_negotiation_trading_value; yesterdays_closing_price_type_code_nxt := yesterdays_closing_price_type_code_nxt_value; yesterdays_closing_price_nxt := yesterdays_closing_price_nxt_value; competition_board_trade_permission_code := competition_board_trade_permission_code_value; negotiation_possible_or_not_before_main_market := negotiation_possible_or_not_before_main_market_value; end_keyword := end_keyword_value |}, bytes)
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 [bound_72 [bound_73 [bound_74 [bound_75 [bound_76 [bound_77 [bound_78 [bound_79 [bound_80 [bound_81 [bound_82 [bound_83 [bound_84 [bound_85 [bound_86 [bound_87 [bound_88 [bound_89 [bound_90 [bound_91 [bound_92 [bound_93 [bound_94 [bound_95 [bound_96 [bound_97 [bound_98 [bound_99 [bound_100 [bound_101 [bound_102 [bound_103 [bound_104 [bound_105 [bound_106 [bound_107 [bound_108 [bound_109 [bound_110 [bound_111 [bound_112 [bound_113 [bound_114 bound_115]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EquitiesBatchDataMessage.

  Module MemberInformationMessage.

    (** Details. *)
    Record t := {
      message_sequence_number : list byte;
      business_date : list byte;
      market_participant_number : list byte;
      name_of_a_market_participant_in_kr : list byte;
      name_of_a_market_participant_in_en : list byte;
      an_abbreviated_name_of_a_market_participant_in_kr : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (business_date record) = 8 /\
      Datatypes.length (market_participant_number record) = 5 /\
      Datatypes.length (name_of_a_market_participant_in_kr record) = 80 /\
      Datatypes.length (name_of_a_market_participant_in_en record) = 80 /\
      Datatypes.length (an_abbreviated_name_of_a_market_participant_in_kr record) = 20 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 8 (business_date record) ++
      encode_bytes 5 (market_participant_number record) ++
      encode_bytes 80 (name_of_a_market_participant_in_kr record) ++
      encode_bytes 80 (name_of_a_market_participant_in_en record) ++
      encode_bytes 20 (an_abbreviated_name_of_a_market_participant_in_kr record) ++
      encode_bytes 1 (end_keyword record).

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
                              match decode_bytes 1 bytes with
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

  End MemberInformationMessage.

  Module IssueEventMessage.

    (** Details. *)
    Record t := {
      message_sequence_number : list byte;
      isin_code : list byte;
      event_type_code : list byte;
      event_reason_code : list byte;
      event_start_date : list byte;
      event_end_date : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_sequence_number record) = 8 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (event_type_code record) = 2 /\
      Datatypes.length (event_reason_code record) = 4 /\
      Datatypes.length (event_start_date record) = 8 /\
      Datatypes.length (event_end_date record) = 8 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (message_sequence_number record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 2 (event_type_code record) ++
      encode_bytes 4 (event_reason_code record) ++
      encode_bytes 8 (event_start_date record) ++
      encode_bytes 8 (event_end_date record) ++
      encode_bytes 1 (end_keyword record).

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
                              match decode_bytes 1 bytes with
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

  End IssueEventMessage.

  Module BlockBasketTradeDataMessage.

    (** Block/Basket Trade Data in NXT. *)
    Record t := {
      board_id : list byte;
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
      accumulated_trading_volume : list byte;
      accumulated_trading_value : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (board_id record) = 2 /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
      Datatypes.length (accumulated_trading_volume record) = 12 /\
      Datatypes.length (accumulated_trading_value record) = 22 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (board_id record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 12 (accumulated_trading_volume record) ++
      encode_bytes 22 (accumulated_trading_value record) ++
      encode_bytes 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (board_id_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (isin_code_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (accumulated_trading_volume_value, bytes) =>
                      match decode_bytes 22 bytes with
                      | None => None
                      | Some (accumulated_trading_value_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (end_keyword_value, bytes) =>
                              Some ({| board_id := board_id_value; isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; accumulated_trading_volume := accumulated_trading_volume_value; accumulated_trading_value := accumulated_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
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

  End BlockBasketTradeDataMessage.

  Module InvestorActivitiesPerAnIssueEodMessage.

    (** Investor Activities per an issue_EOD. *)
    Record t := {
      isin_code : list byte;
      a_designated_number_for_an_issue_from_krx : list byte;
      investor_code : list byte;
      accumulated_ask_trading_volume : list byte;
      accumulated_ask_trading_value : list byte;
      accumulated_bid_trading_volume : list byte;
      accumulated_bid_trading_value : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (a_designated_number_for_an_issue_from_krx record) = 6 /\
      Datatypes.length (investor_code record) = 4 /\
      Datatypes.length (accumulated_ask_trading_volume record) = 12 /\
      Datatypes.length (accumulated_ask_trading_value record) = 22 /\
      Datatypes.length (accumulated_bid_trading_volume record) = 12 /\
      Datatypes.length (accumulated_bid_trading_value record) = 22 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 6 (a_designated_number_for_an_issue_from_krx record) ++
      encode_bytes 4 (investor_code record) ++
      encode_bytes 12 (accumulated_ask_trading_volume record) ++
      encode_bytes 22 (accumulated_ask_trading_value record) ++
      encode_bytes 12 (accumulated_bid_trading_volume record) ++
      encode_bytes 22 (accumulated_bid_trading_value record) ++
      encode_bytes 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (a_designated_number_for_an_issue_from_krx_value, bytes) =>
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
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (end_keyword_value, bytes) =>
                                      Some ({| isin_code := isin_code_value; a_designated_number_for_an_issue_from_krx := a_designated_number_for_an_issue_from_krx_value; investor_code := investor_code_value; accumulated_ask_trading_volume := accumulated_ask_trading_volume_value; accumulated_ask_trading_value := accumulated_ask_trading_value_value; accumulated_bid_trading_volume := accumulated_bid_trading_volume_value; accumulated_bid_trading_value := accumulated_bid_trading_value_value; end_keyword := end_keyword_value |}, bytes)
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

  End InvestorActivitiesPerAnIssueEodMessage.

  Module ShortSellingMessage.

    (** Short Selling. *)
    Record t := {
      isin_code : list byte;
      covered_short_selling_trading_volume : list byte;
      covered_short_selling_trading_value : list byte;
      uptick_rule_applied_covered_short_selling_trading_volume : list byte;
      uptick_rule_applied_covered_short_selling_trading_value : list byte;
      uptick_rule_unapplied_covered_short_selling_trading_volume : list byte;
      uptick_rule_unapplied_covered_short_selling_trading_value : list byte;
      end_keyword : list byte;
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
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 12 (covered_short_selling_trading_volume record) ++
      encode_bytes 22 (covered_short_selling_trading_value record) ++
      encode_bytes 12 (uptick_rule_applied_covered_short_selling_trading_volume record) ++
      encode_bytes 22 (uptick_rule_applied_covered_short_selling_trading_value record) ++
      encode_bytes 12 (uptick_rule_unapplied_covered_short_selling_trading_volume record) ++
      encode_bytes 22 (uptick_rule_unapplied_covered_short_selling_trading_value record) ++
      encode_bytes 1 (end_keyword record).

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
                                  match decode_bytes 1 bytes with
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

  End ShortSellingMessage.

  Module BrokersAcitityInformationMessage.

    (** Information on Brokers Activity in NXT market. *)
    Record t := {
      isin_code : list byte;
      member_number : list byte;
      accumulated_ask_trading_volume : list byte;
      accumulated_ask_trading_value : list byte;
      accumulated_bid_trading_volume : list byte;
      accumulated_bid_trading_value : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (member_number record) = 5 /\
      Datatypes.length (accumulated_ask_trading_volume record) = 12 /\
      Datatypes.length (accumulated_ask_trading_value record) = 22 /\
      Datatypes.length (accumulated_bid_trading_volume record) = 12 /\
      Datatypes.length (accumulated_bid_trading_value record) = 22 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 5 (member_number record) ++
      encode_bytes 12 (accumulated_ask_trading_volume record) ++
      encode_bytes 22 (accumulated_ask_trading_value record) ++
      encode_bytes 12 (accumulated_bid_trading_volume record) ++
      encode_bytes 22 (accumulated_bid_trading_value record) ++
      encode_bytes 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (member_number_value, bytes) =>
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
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (end_keyword_value, bytes) =>
                                  Some ({| isin_code := isin_code_value; member_number := member_number_value; accumulated_ask_trading_volume := accumulated_ask_trading_volume_value; accumulated_ask_trading_value := accumulated_ask_trading_value_value; accumulated_bid_trading_volume := accumulated_bid_trading_volume_value; accumulated_bid_trading_value := accumulated_bid_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 86.
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

  End BrokersAcitityInformationMessage.

  Module TradingActivityBySessionPerAnIssueMessage.

    (** Trading Activity by session for each issue and market. *)
    Record t := {
      isin_code : list byte;
      total_number_of_tradable_issues_on_competitive_trading : list byte;
      pre_market_accumulated_trading_volume : list byte;
      pre_market_accumulated_trading_value : list byte;
      main_market_accumulated_trading_volume : list byte;
      main_market_accumulated_trading_value : list byte;
      after_market_accumulated_trading_volume : list byte;
      after_market_accumulated_trading_value : list byte;
      end_keyword : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (total_number_of_tradable_issues_on_competitive_trading record) = 5 /\
      Datatypes.length (pre_market_accumulated_trading_volume record) = 12 /\
      Datatypes.length (pre_market_accumulated_trading_value record) = 22 /\
      Datatypes.length (main_market_accumulated_trading_volume record) = 12 /\
      Datatypes.length (main_market_accumulated_trading_value record) = 22 /\
      Datatypes.length (after_market_accumulated_trading_volume record) = 12 /\
      Datatypes.length (after_market_accumulated_trading_value record) = 22 /\
      Datatypes.length (end_keyword record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (isin_code record) ++
      encode_bytes 5 (total_number_of_tradable_issues_on_competitive_trading record) ++
      encode_bytes 12 (pre_market_accumulated_trading_volume record) ++
      encode_bytes 22 (pre_market_accumulated_trading_value record) ++
      encode_bytes 12 (main_market_accumulated_trading_volume record) ++
      encode_bytes 22 (main_market_accumulated_trading_value record) ++
      encode_bytes 12 (after_market_accumulated_trading_volume record) ++
      encode_bytes 22 (after_market_accumulated_trading_value record) ++
      encode_bytes 1 (end_keyword record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (isin_code_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (total_number_of_tradable_issues_on_competitive_trading_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (pre_market_accumulated_trading_volume_value, bytes) =>
                  match decode_bytes 22 bytes with
                  | None => None
                  | Some (pre_market_accumulated_trading_value_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (main_market_accumulated_trading_volume_value, bytes) =>
                          match decode_bytes 22 bytes with
                          | None => None
                          | Some (main_market_accumulated_trading_value_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (after_market_accumulated_trading_volume_value, bytes) =>
                                  match decode_bytes 22 bytes with
                                  | None => None
                                  | Some (after_market_accumulated_trading_value_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (end_keyword_value, bytes) =>
                                          Some ({| isin_code := isin_code_value; total_number_of_tradable_issues_on_competitive_trading := total_number_of_tradable_issues_on_competitive_trading_value; pre_market_accumulated_trading_volume := pre_market_accumulated_trading_volume_value; pre_market_accumulated_trading_value := pre_market_accumulated_trading_value_value; main_market_accumulated_trading_volume := main_market_accumulated_trading_volume_value; main_market_accumulated_trading_value := main_market_accumulated_trading_value_value; after_market_accumulated_trading_volume := after_market_accumulated_trading_volume_value; after_market_accumulated_trading_value := after_market_accumulated_trading_value_value; end_keyword := end_keyword_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 120.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingActivityBySessionPerAnIssueMessage.

End NextradeEtpCommonV212.
