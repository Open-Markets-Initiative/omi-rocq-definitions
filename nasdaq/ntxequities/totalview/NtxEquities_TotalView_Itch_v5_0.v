From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) TX TotalView Itch

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

Module NtxEquitiesTotalViewV50.

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

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (event_code_value, bytes) =>
                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; event_code := event_code_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module StockDirectoryMessage.

    (** At the start of each trading day, Nasdaq Texas disseminates stock directory messages for all active symbols in the Nasdaq Texas execution system. *)
    Record t := {
      stock_locate : N;
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
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
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
      encode_uint 2 (stock_locate record) ++
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
      | Some (stock_locate_value, bytes) =>
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
                                                                          Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; market_category := market_category_value; financial_status_indicator := financial_status_indicator_value; round_lot_size := round_lot_size_value; round_lots_only := round_lots_only_value; issue_classification := issue_classification_value; issue_sub_type := issue_sub_type_value; authenticity := authenticity_value; short_sale_threshold_indicator := short_sale_threshold_indicator_value; ipo_flag := ipo_flag_value; luld_reference_price_tier := luld_reference_price_tier_value; etp_flag := etp_flag_value; etp_leverage_factor := etp_leverage_factor_value; inverse_indicator := inverse_indicator_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockDirectoryMessage.

  Module StockTradingActionMessage.

    (** Nasdaq Texas uses this administrative message to indicate the current trading status of a security to the trading community. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      trading_state : list byte;
      reserved : list byte;
      trading_action_reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (reserved record) = 1 /\
      Datatypes.length (trading_action_reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (reserved record) ++
      encode_bytes 4 (trading_action_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
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
                      | Some (trading_state_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (trading_action_reason_value, bytes) =>
                                  Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; trading_state := trading_state_value; reserved := reserved_value; trading_action_reason := trading_action_reason_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockTradingActionMessage.

  Module RegShoShortSalePriceTestRestrictedIndicatorMessage.

    (** In February 2011, the Securities and Exchange Commission (SEC) implemented changes to Rule 201 of the Regulation SHO (Reg SHO). *)
    Record t := {
      locate_code : N;
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (locate_code record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (locate_code record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (locate_code_value, bytes) =>
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
                          Some ({| locate_code := locate_code_value; tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; reg_sho_action := reg_sho_action_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegShoShortSalePriceTestRestrictedIndicatorMessage.

  Module MarketParticipantPositionMessage.

    (** At the start of each trading day, Nasdaq Texas disseminates a spin of market participant position messages. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      mpid : list byte;
      stock : list byte;
      primary_market_maker : list byte;
      market_maker_mode : list byte;
      market_participant_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (mpid record) = 4 /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (primary_market_maker record) = 1 /\
      Datatypes.length (market_maker_mode record) = 1 /\
      Datatypes.length (market_participant_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 4 (mpid record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (primary_market_maker record) ++
      encode_bytes 1 (market_maker_mode record) ++
      encode_bytes 1 (market_participant_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (mpid_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (stock_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (primary_market_maker_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (market_maker_mode_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (market_participant_state_value, bytes) =>
                                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; mpid := mpid_value; stock := stock_value; primary_market_maker := primary_market_maker_value; market_maker_mode := market_maker_mode_value; market_participant_state := market_participant_state_value |}, bytes)
                                  end
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketParticipantPositionMessage.

  Module MwcbDeclineLevelMessage.

    (** Informs data recipients what the daily MWCB breach points are set to for the current trading day. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      level_1 : N;
      level_2 : N;
      level_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (level_1 record < 256 ^ N.of_nat 8)%N /\
      (level_2 record < 256 ^ N.of_nat 8)%N /\
      (level_3 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (level_1 record) ++
      encode_uint 8 (level_2 record) ++
      encode_uint 8 (level_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (level_1_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (level_2_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (level_3_value, bytes) =>
                              Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; level_1 := level_1_value; level_2 := level_2_value; level_3 := level_3_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MwcbDeclineLevelMessage.

  Module MwcbStatusMessage.

    (** Informs data recipients when a MWCB has breached one of the established levels *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      breached_level : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (breached_level record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (breached_level record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (breached_level_value, bytes) =>
                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; breached_level := breached_level_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MwcbStatusMessage.

  Module LuldAuctionCollarMessage.

    (** Indicates the auction collar thresholds within which a paused security can reopen following a LULD Trading Pause *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      auction_collar_reference_price : N;
      upper_auction_collar_price : N;
      lower_auction_collar_price : N;
      auction_collar_extension : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      (auction_collar_reference_price record < 256 ^ N.of_nat 4)%N /\
      (upper_auction_collar_price record < 256 ^ N.of_nat 4)%N /\
      (lower_auction_collar_price record < 256 ^ N.of_nat 4)%N /\
      (auction_collar_extension record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (auction_collar_reference_price record) ++
      encode_uint 4 (upper_auction_collar_price record) ++
      encode_uint 4 (lower_auction_collar_price record) ++
      encode_uint 4 (auction_collar_extension record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
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
                      | Some (auction_collar_reference_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (upper_auction_collar_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (lower_auction_collar_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (auction_collar_extension_value, bytes) =>
                                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; auction_collar_reference_price := auction_collar_reference_price_value; upper_auction_collar_price := upper_auction_collar_price_value; lower_auction_collar_price := lower_auction_collar_price_value; auction_collar_extension := auction_collar_extension_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LuldAuctionCollarMessage.

  Module OperationalHaltMessage.

    (** The Exchange uses this message to indicate the current Operational Status of a security to the trading community. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      market_code : list byte;
      operational_halt_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (market_code record) = 1 /\
      Datatypes.length (operational_halt_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (market_code record) ++
      encode_bytes 1 (operational_halt_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
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
                      | Some (market_code_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (operational_halt_action_value, bytes) =>
                              Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; market_code := market_code_value; operational_halt_action := operational_halt_action_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OperationalHaltMessage.

  Module AddOrderNoMpidAttributionMessage.

    (** This message will be generated for unattributed orders accepted by the Nasdaq Texas system. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      shares : N;
      stock : list byte;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (buy_sell_indicator_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (shares_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (stock_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderNoMpidAttributionMessage.

  Module AddOrderMpidAttributionMessage.

    (** This message will be generated for attributed orders and quotations accepted by the Nasdaq Texas system. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      shares : N;
      stock : list byte;
      price : N;
      attribution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (attribution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (price record) ++
      encode_bytes 4 (attribution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (buy_sell_indicator_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (shares_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (stock_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (attribution_value, bytes) =>
                                          Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value; attribution := attribution_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMpidAttributionMessage.

  Module OrderExecutedMessage.

    (** This message is sent whenever an order on the book is executed in whole or in part. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      executed_shares : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (executed_shares record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (executed_shares record) ++
      encode_uint 8 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (executed_shares_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; executed_shares := executed_shares_value; match_number := match_number_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** This message is sent whenever an order on the book is executed in whole or in part at a price different from the initial display price. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      executed_shares : N;
      match_number : N;
      printable : list byte;
      execution_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (executed_shares record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (printable record) = 1 /\
      (execution_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (executed_shares record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (execution_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (executed_shares_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (printable_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (execution_price_value, bytes) =>
                                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; executed_shares := executed_shares_value; match_number := match_number_value; printable := printable_value; execution_price := execution_price_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceMessage.

  Module OrderCancelMessage.

    (** This message is sent whenever an order on the book is modified as a result of a partial cancellation *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      cancelled_shares : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (cancelled_shares record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (cancelled_shares record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (cancelled_shares_value, bytes) =>
                          Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; cancelled_shares := cancelled_shares_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderCancelMessage.

  Module OrderDeleteMessage.

    (** This message is sent whenever an order on the book is being cancelled. All remaining shares are no longer accessible so the order must be removed from the book. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderDeleteMessage.

  Module OrderReplaceMessage.

    (** This message is sent whenever an order on the book has been cancel-replaced. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      original_order_reference_number : N;
      new_order_reference_number : N;
      shares : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (original_order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (new_order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (original_order_reference_number record) ++
      encode_uint 8 (new_order_reference_number record) ++
      encode_uint 4 (shares record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (original_order_reference_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (new_order_reference_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (shares_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; original_order_reference_number := original_order_reference_number_value; new_order_reference_number := new_order_reference_number_value; shares := shares_value; price := price_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderReplaceMessage.

  Module NonCrossTradeMessage.

    (** The Trade Message is designed to provide execution details for normal match events involving non-displayable order types. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      order_reference_number : N;
      buy_sell_indicator : list byte;
      shares : N;
      stock : list byte;
      price : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_sell_indicator record) = 1 /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stock record) = 8 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (buy_sell_indicator record) ++
      encode_uint 4 (shares record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (buy_sell_indicator_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (shares_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (stock_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (match_number_value, bytes) =>
                                          Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; order_reference_number := order_reference_number_value; buy_sell_indicator := buy_sell_indicator_value; shares := shares_value; stock := stock_value; price := price_value; match_number := match_number_value |}, bytes)
                                      end
                                  end
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NonCrossTradeMessage.

  Module CrossTradeMessage.

    (** Cross Trade message indicates that Nasdaq Texas has completed its cross process for a specific security. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      shares_long : N;
      stock : list byte;
      cross_price : N;
      match_number : N;
      cross_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (shares_long record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (stock record) = 8 /\
      (cross_price record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cross_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (shares_long record) ++
      encode_bytes 8 (stock record) ++
      encode_uint 4 (cross_price record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (cross_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (shares_long_value, bytes) =>
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
                                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; shares_long := shares_long_value; stock := stock_value; cross_price := cross_price_value; match_number := match_number_value; cross_type := cross_type_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CrossTradeMessage.

  Module BrokenTradeMessage.

    (** The Broken Trade Message is sent whenever an execution on Nasdaq Texas is broken. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_uint 8 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 6 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; match_number := match_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BrokenTradeMessage.

  Module NetOrderImbalanceIndicatorMessage.

    (** Nasdaq Texas disseminates NOII data at 5-second intervals in the minutes leading up to the Nasdaq Opening Cross and Nasdaq Closing Cross. *)
    Record t := {
      stock_locate : N;
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
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
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
      encode_uint 2 (stock_locate record) ++
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
      | Some (stock_locate_value, bytes) =>
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
                                                      Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; paired_shares := paired_shares_value; imbalance_shares := imbalance_shares_value; imbalance_direction := imbalance_direction_value; stock := stock_value; far_price := far_price_value; near_price := near_price_value; current_reference_price := current_reference_price_value; cross_type := cross_type_value; price_variation_indicator := price_variation_indicator_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetOrderImbalanceIndicatorMessage.

  Module RetailInterestMessage.

    (** Indicates price improving interest of the Bid, Ask or both the Bid and Ask for a security. *)
    Record t := {
      stock_locate : N;
      tracking_number : N;
      timestamp : N;
      stock : list byte;
      interest_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stock_locate record < 256 ^ N.of_nat 2)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (stock record) = 8 /\
      Datatypes.length (interest_flag record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stock_locate record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 6 (timestamp record) ++
      encode_bytes 8 (stock record) ++
      encode_bytes 1 (interest_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stock_locate_value, bytes) =>
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
                      | Some (interest_flag_value, bytes) =>
                          Some ({| stock_locate := stock_locate_value; tracking_number := tracking_number_value; timestamp := timestamp_value; stock := stock_value; interest_flag := interest_flag_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetailInterestMessage.

End NtxEquitiesTotalViewV50.
