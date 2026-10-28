From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Net Order Imbalance View

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

Module NsmEquitiesNoiViewV3020262.

  Module PacketHeader.

    (** Itch Mold Udp 64 Packet Header *)
    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

    (** Mold Udp 64 Message Header *)
    Record t := {
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module SystemEvent.

    (** Signals a market or data feed handler event *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; event_code := event_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEvent.

  Module StockDirectoryMessage.

    (** Disseminates stock directory info for all active symbols at start of trading day *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      market_category : list byte;
      financial_status_indicator : list byte;
      round_lot_size : N;
      round_lots_only : list byte;
      issue_classification : list byte;
      issue_sub_type : list byte;
      authenticity : list byte;
      short_sale_threshold_indicator : list byte;
      ipo_flag : list byte;
      luld_reference_price_tier : list byte;
      etp_flag : list byte;
      etp_leverage_factor : N;
      inverse_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (market_category record) = 1 /\
      Datatypes.length (financial_status_indicator record) = 1 /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (round_lots_only record) = 1 /\
      Datatypes.length (issue_classification record) = 1 /\
      Datatypes.length (issue_sub_type record) = 2 /\
      Datatypes.length (authenticity record) = 1 /\
      Datatypes.length (short_sale_threshold_indicator record) = 1 /\
      Datatypes.length (ipo_flag record) = 1 /\
      Datatypes.length (luld_reference_price_tier record) = 1 /\
      Datatypes.length (etp_flag record) = 1 /\
      (etp_leverage_factor record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (inverse_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (market_category record) ++
      encode_bytes 1 (financial_status_indicator record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_bytes 1 (round_lots_only record) ++
      encode_bytes 1 (issue_classification record) ++
      encode_bytes 2 (issue_sub_type record) ++
      encode_bytes 1 (authenticity record) ++
      encode_bytes 1 (short_sale_threshold_indicator record) ++
      encode_bytes 1 (ipo_flag record) ++
      encode_bytes 1 (luld_reference_price_tier record) ++
      encode_bytes 1 (etp_flag record) ++
      encode_uint 4 (etp_leverage_factor record) ++
      encode_bytes 1 (inverse_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (stock_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_category_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (financial_status_indicator_value, bytes) =>
                          match decode_uint 4 bytes with
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
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (etp_leverage_factor_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (inverse_indicator_value, bytes) =>
                                                                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value; round_lot_size := round_lot_size_value; round_lots_only := round_lots_only_value; issue_classification := issue_classification_value; issue_sub_type := issue_sub_type_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; ipo_flag := ipo_flag_value; luld_reference_price_tier := luld_reference_price_tier_value; etp_flag := etp_flag_value; etp_leverage_factor := etp_leverage_factor_value; inverse_indicator := inverse_indicator_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockDirectoryMessage.

  Module StockTradingActionMessage.

    (** Indicates the current trading status of a security *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      current_trading_state : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (current_trading_state record) = 1 /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (current_trading_state record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (stock_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (current_trading_state_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (reason_value, bytes) =>
                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; current_trading_state := current_trading_state_value; reason := reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockTradingActionMessage.

  Module RegShoShortSalePriceTestRestrictedIndicatorMessage.

    (** Indicates Rule 201 Reg SHO restriction status for a security *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (stock_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reg_sho_action_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; reg_sho_action := reg_sho_action_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegShoShortSalePriceTestRestrictedIndicatorMessage.

  Module NetOrderImbalanceIndicatorMessage.

    (** Net Order Imbalance Indicator for Opening, Closing, and Extended Trading crosses *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      paired_shares : N;
      imbalance_shares : N;
      imbalance_direction : list byte;
      stock : list byte;
      far_price : N;
      near_price : N;
      current_reference_price : N;
      cross_type : list byte;
      price_variation_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (paired_shares record < 256 ^ N.of_nat 8)%N /\
      (imbalance_shares record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (imbalance_direction record) = 1 /\
      Datatypes.length (stock record) = 8 /\
      (far_price record < 256 ^ N.of_nat 4)%N /\
      (near_price record < 256 ^ N.of_nat 4)%N /\
      (current_reference_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (price_variation_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (paired_shares record) ++
      encode_uint 8 (imbalance_shares record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (far_price record) ++
      encode_uint 4 (near_price record) ++
      encode_uint 4 (current_reference_price record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (price_variation_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (paired_shares_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (imbalance_shares_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (imbalance_direction_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (stock_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (far_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (near_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (current_reference_price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cross_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (price_variation_indicator_value, bytes) =>
                                                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; paired_shares := paired_shares_value; imbalance_shares := imbalance_shares_value; imbalance_direction := imbalance_direction_value; stock := stock_value; far_price := far_price_value; near_price := near_price_value; current_reference_price := current_reference_price_value; cross_type := cross_type_value; price_variation_indicator := price_variation_indicator_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetOrderImbalanceIndicatorMessage.

  Module CrossTradeMessage.

    (** Indicates Nasdaq has completed its cross process for a specific security *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      shares : N;
      stock : list byte;
      cross_price : N;
      match_number : N;
      cross_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (shares record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (stock record) = 8 /\
      (cross_price record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cross_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (cross_price record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (cross_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (shares_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (stock_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (cross_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cross_type_value, bytes) =>
                                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; shares := shares_value; stock := stock_value; cross_price := cross_price_value; match_number := match_number_value; cross_type := cross_type_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CrossTradeMessage.

  Module IpoQuotingPeriodUpdateMessage.

    (** Indicates the anticipated IPO quotation release time of a security *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      ipo_quotation_release_time : N;
      ipo_quotation_release_qualifier : list byte;
      ipo_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      (ipo_quotation_release_time record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ipo_quotation_release_qualifier record) = 1 /\
      (ipo_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (ipo_quotation_release_time record) ++
      encode_bytes 1 (ipo_quotation_release_qualifier record) ++
      encode_uint 4 (ipo_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (stock_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (ipo_quotation_release_time_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (ipo_quotation_release_qualifier_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ipo_price_value, bytes) =>
                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; ipo_quotation_release_time := ipo_quotation_release_time_value; ipo_quotation_release_qualifier := ipo_quotation_release_qualifier_value; ipo_price := ipo_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IpoQuotingPeriodUpdateMessage.

  Module DirectListingWithCapitalRaisePriceDiscoveryMessage.

    (** Disseminated for DLCR securities once volatility test has passed *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      open_eligibility_status : list byte;
      minimum_allowable_price : N;
      maximum_allowable_price : N;
      near_execution_price : N;
      near_execution_time : N;
      lower_price_range_collar : N;
      upper_price_range_collar : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (open_eligibility_status record) = 1 /\
      (minimum_allowable_price record < 256 ^ N.of_nat 4)%N /\
      (maximum_allowable_price record < 256 ^ N.of_nat 4)%N /\
      (near_execution_price record < 256 ^ N.of_nat 4)%N /\
      (near_execution_time record < 256 ^ N.of_nat 8)%N /\
      (lower_price_range_collar record < 256 ^ N.of_nat 4)%N /\
      (upper_price_range_collar record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (open_eligibility_status record) ++
      encode_uint 4 (minimum_allowable_price record) ++
      encode_uint 4 (maximum_allowable_price record) ++
      encode_uint 4 (near_execution_price record) ++
      encode_uint 8 (near_execution_time record) ++
      encode_uint 4 (lower_price_range_collar record) ++
      encode_uint 4 (upper_price_range_collar record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (stock_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (open_eligibility_status_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (minimum_allowable_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (maximum_allowable_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (near_execution_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (near_execution_time_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (lower_price_range_collar_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (upper_price_range_collar_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; open_eligibility_status := open_eligibility_status_value; minimum_allowable_price := minimum_allowable_price_value; maximum_allowable_price := maximum_allowable_price_value; near_execution_price := near_execution_price_value; near_execution_time := near_execution_time_value; lower_price_range_collar := lower_price_range_collar_value; upper_price_range_collar := upper_price_range_collar_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DirectListingWithCapitalRaisePriceDiscoveryMessage.

End NsmEquitiesNoiViewV3020262.
