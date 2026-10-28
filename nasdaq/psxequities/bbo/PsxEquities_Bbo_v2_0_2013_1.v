From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Best Bid And Offer

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
      - a run counted by a field
  *)

Module PsxEquitiesBboV2020131.

  Module PacketHeader.

    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      timestamp : list byte;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (timestamp record) = 8 /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (timestamp record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| timestamp := timestamp_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module SystemEventMessage.

    (** The System Event message is used to signal key market or data feed control events. *)
    Record t := {
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (event_code_value, bytes) =>
          Some ({| event_code := event_code_value |}, bytes)
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

  End SystemEventMessage.

  Module StockDirectoryMessage.

    (** At the start of each trading day, NASDAQ PSX disseminates stock directory messages for all active symbols in its market center system. *)
    Record t := {
      stock : list byte;
      market_category : list byte;
      financial_status_indicator : list byte;
      round_lot_size : list byte;
      round_lots_only : list byte;
      issue_classification : list byte;
      issue_sub_type : list byte;
      authenticity : list byte;
      short_sale_threshold_indicator : list byte;
      ipo_flag : list byte;
      luld_reference_price_tier : list byte;
      etp_flag : list byte;
      etp_leverage_factor : list byte;
      inverse_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      Datatypes.length (round_lot_size record) = 6 /\
      Datatypes.length (round_lots_only record) = 1 /\
      Datatypes.length (issue_classification record) = 1 /\
      Datatypes.length (issue_sub_type record) = 2 /\
      Datatypes.length (authenticity record) = 1 /\
      Datatypes.length (short_sale_threshold_indicator record) = 1 /\
      Datatypes.length (ipo_flag record) = 1 /\
      Datatypes.length (luld_reference_price_tier record) = 1 /\
      Datatypes.length (etp_flag record) = 1 /\
      Datatypes.length (etp_leverage_factor record) = 5 /\
      Datatypes.length (inverse_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (market_category record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_bytes 6 (round_lot_size record) ++
      encode_bytes 1 (round_lots_only record) ++
      encode_bytes 1 (issue_classification record) ++
      encode_bytes 2 (issue_sub_type record) ++
      encode_bytes 1 (authenticity record) ++
      encode_bytes 1 (short_sale_threshold_indicator record) ++
      encode_bytes 1 (ipo_flag record) ++
      encode_bytes 1 (luld_reference_price_tier record) ++
      encode_bytes 1 (etp_flag record) ++
      encode_bytes 5 (etp_leverage_factor record) ++
      encode_bytes 1 (inverse_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_category_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (financial_status_indicator_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (round_lot_size_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (round_lots_only_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (issue_classification_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (issue_sub_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (authenticity_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (short_sale_threshold_indicator_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (ipo_flag_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (luld_reference_price_tier_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (etp_flag_value, bytes) =>
                                                      match decode_bytes 5 bytes with
                                                      | None => None
                                                      | Some (etp_leverage_factor_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (inverse_indicator_value, bytes) =>
                                                              Some ({| stock := stock_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value; round_lot_size := round_lot_size_value; round_lots_only := round_lots_only_value; issue_classification := issue_classification_value; issue_sub_type := issue_sub_type_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; ipo_flag := ipo_flag_value; luld_reference_price_tier := luld_reference_price_tier_value; etp_flag := etp_flag_value; etp_leverage_factor := etp_leverage_factor_value; inverse_indicator := inverse_indicator_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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

  End StockDirectoryMessage.

  Module StockTradingActionMessage.

    (** NASDAQ OMX uses this administrative message to indicate the current trading status of a security to the trading community. *)
    Record t := {
      stock : list byte;
      security_class : list byte;
      current_trading_state : list byte;
      reason : list byte;
      tracking_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (current_trading_state record) = 1 /\
      Datatypes.length (reason record) = 4 /\
      Datatypes.length (tracking_id record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 1 (current_trading_state record) ++
      encode_bytes 4 (reason record) ++
      encode_bytes 13 (tracking_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (security_class_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (current_trading_state_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      match decode_bytes 13 bytes with
                      | None => None
                      | Some (tracking_id_value, bytes) =>
                          Some ({| stock := stock_value; security_class := security_class_value; current_trading_state := current_trading_state_value; reason := reason_value; tracking_id := tracking_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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

  End StockTradingActionMessage.

  Module RegShoShortSalePriceTestRestrictedIndicatorMessage.

    (** Denotes the Reg SHO Short Sale Price Test Restriction (Rule 201) status for an issue: a full pre-opening spin for NASDAQ-listed issues and intraday status changes. *)
    Record t := {
      stock : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reg_sho_action_value, bytes) =>
              Some ({| stock := stock_value; reg_sho_action := reg_sho_action_value |}, bytes)
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

  End RegShoShortSalePriceTestRestrictedIndicatorMessage.

  Module MwcbDeclineLevelMessage.

    (** Informs data recipients what the daily MWCB breach points are set to for the current trading day. *)
    Record t := {
      level_1 : list byte;
      level_2 : list byte;
      level_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (level_1 record) = 12 /\
      Datatypes.length (level_2 record) = 12 /\
      Datatypes.length (level_3 record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (level_1 record) ++
      encode_bytes 12 (level_2 record) ++
      encode_bytes 12 (level_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (level_1_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (level_2_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (level_3_value, bytes) =>
                  Some ({| level_1 := level_1_value; level_2 := level_2_value; level_3 := level_3_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End MwcbDeclineLevelMessage.

  Module MwcbStatusMessage.

    (** Informs data recipients when a MWCB has breached one of the established levels. *)
    Record t := {
      breached_level : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (breached_level record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (breached_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (breached_level_value, bytes) =>
          Some ({| breached_level := breached_level_value |}, bytes)
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

  End MwcbStatusMessage.

  Module QuotationMessage.

    (** PSX BBO will broadcast a real-time update every time that the exchange's best bid and offer quote is updated during the trading day. *)
    Record t := {
      stock : list byte;
      security_class : list byte;
      psx_best_bid_price : list byte;
      psx_best_bid_size : list byte;
      psx_best_offer_price : list byte;
      psx_best_offer_size : list byte;
      tracking_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (security_class record) = 1 /\
      Datatypes.length (psx_best_bid_price record) = 10 /\
      Datatypes.length (psx_best_bid_size record) = 9 /\
      Datatypes.length (psx_best_offer_price record) = 10 /\
      Datatypes.length (psx_best_offer_size record) = 9 /\
      Datatypes.length (tracking_id record) = 13.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (security_class record) ++
      encode_bytes 10 (psx_best_bid_price record) ++
      encode_bytes 9 (psx_best_bid_size record) ++
      encode_bytes 10 (psx_best_offer_price record) ++
      encode_bytes 9 (psx_best_offer_size record) ++
      encode_bytes 13 (tracking_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (stock_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (security_class_value, bytes) =>
              match decode_bytes 10 bytes with
              | None => None
              | Some (psx_best_bid_price_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (psx_best_bid_size_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (psx_best_offer_price_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (psx_best_offer_size_value, bytes) =>
                              match decode_bytes 13 bytes with
                              | None => None
                              | Some (tracking_id_value, bytes) =>
                                  Some ({| stock := stock_value; security_class := security_class_value; psx_best_bid_price := psx_best_bid_price_value; psx_best_bid_size := psx_best_bid_size_value; psx_best_offer_price := psx_best_offer_price_value; psx_best_offer_size := psx_best_offer_size_value; tracking_id := tracking_id_value |}, bytes)
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

  End QuotationMessage.

End PsxEquitiesBboV2020131.
