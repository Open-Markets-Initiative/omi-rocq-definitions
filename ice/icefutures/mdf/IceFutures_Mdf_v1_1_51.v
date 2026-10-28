From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Intercontinental Exchange Multicast Data Feed

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
      - a run counted by a field
      - a field read in bits
      - a field of no fixed width
  *)

Module IceFuturesMdfV1151.

  Module PacketHeader.

    (** iMpact Upd market data packet header *)
    Record t := {
      session : N;
      sequence : N;
      number_of_msgs : N;
      sent_date_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session record < 256 ^ N.of_nat 2)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N /\
      (number_of_msgs record < 256 ^ N.of_nat 2)%N /\
      (sent_date_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (session record) ++
      encode_uint 4 (sequence record) ++
      encode_uint 2 (number_of_msgs record) ++
      encode_uint 8 (sent_date_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (number_of_msgs_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (sent_date_time_value, bytes) =>
                      Some ({| session := session_value; sequence := sequence_value; number_of_msgs := number_of_msgs_value; sent_date_time := sent_date_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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

  End PacketHeader.

  Module MessageHeader.

    (** iMpact message header *)
    Record t := {
      message_type : list byte;
      length_ : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_type record) = 1 /\
      (length_ record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_type record) ++
      encode_uint 2 (length_ record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (length__value, bytes) =>
              Some ({| message_type := message_type_value; length_ := length__value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End MessageHeader.

  Module MarketSnapshotMessage.

    (** The market snapshot message is the same for full order depth and price level snapshot channel. *)
    Record t := {
      market_id : N;
      market_type : N;
      trading_status : list byte;
      volume : N;
      block_volume : N;
      efs_volume : N;
      efp_volume : N;
      open_interest : N;
      opening_price : N;
      settlement_price_with_deal_price_precision : N;
      high : N;
      low : N;
      vwap : N;
      num_of_book_entries : N;
      last_trade_price : N;
      last_trade_quantity : N;
      last_trade_date_time : N;
      settle_price_date_time : N;
      last_message_sequence_id : N;
      reserved_2 : N;
      open_interest_date : list byte;
      is_settle_price_official : list byte;
      settlement_price : N;
      has_previous_day_settlement_price : list byte;
      previous_day_settlement_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (market_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (trading_status record) = 1 /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (block_volume record < 256 ^ N.of_nat 4)%N /\
      (efs_volume record < 256 ^ N.of_nat 4)%N /\
      (efp_volume record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 4)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_price_with_deal_price_precision record < 256 ^ N.of_nat 8)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (num_of_book_entries record < 256 ^ N.of_nat 4)%N /\
      (last_trade_price record < 256 ^ N.of_nat 8)%N /\
      (last_trade_quantity record < 256 ^ N.of_nat 4)%N /\
      (last_trade_date_time record < 256 ^ N.of_nat 8)%N /\
      (settle_price_date_time record < 256 ^ N.of_nat 8)%N /\
      (last_message_sequence_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (open_interest_date record) = 10 /\
      Datatypes.length (is_settle_price_official record) = 1 /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (has_previous_day_settlement_price record) = 1 /\
      (previous_day_settlement_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 2 (market_type record) ++
      encode_bytes 1 (trading_status record) ++
      encode_uint 4 (volume record) ++
      encode_uint 4 (block_volume record) ++
      encode_uint 4 (efs_volume record) ++
      encode_uint 4 (efp_volume record) ++
      encode_uint 4 (open_interest record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (settlement_price_with_deal_price_precision record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 4 (num_of_book_entries record) ++
      encode_uint 8 (last_trade_price record) ++
      encode_uint 4 (last_trade_quantity record) ++
      encode_uint 8 (last_trade_date_time record) ++
      encode_uint 8 (settle_price_date_time record) ++
      encode_uint 4 (last_message_sequence_id record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_bytes 10 (open_interest_date record) ++
      encode_bytes 1 (is_settle_price_official record) ++
      encode_uint 8 (settlement_price record) ++
      encode_bytes 1 (has_previous_day_settlement_price record) ++
      encode_uint 8 (previous_day_settlement_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (market_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (block_volume_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (efs_volume_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (efp_volume_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (open_interest_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (opening_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (settlement_price_with_deal_price_precision_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (high_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (low_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (vwap_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (num_of_book_entries_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (last_trade_price_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (last_trade_quantity_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (last_trade_date_time_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (settle_price_date_time_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (last_message_sequence_id_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (reserved_2_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (open_interest_date_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (is_settle_price_official_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (settlement_price_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (has_previous_day_settlement_price_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (previous_day_settlement_price_value, bytes) =>
                                                                                                          Some ({| market_id := market_id_value; market_type := market_type_value; trading_status := trading_status_value; volume := volume_value; block_volume := block_volume_value; efs_volume := efs_volume_value; efp_volume := efp_volume_value; open_interest := open_interest_value; opening_price := opening_price_value; settlement_price_with_deal_price_precision := settlement_price_with_deal_price_precision_value; high := high_value; low := low_value; vwap := vwap_value; num_of_book_entries := num_of_book_entries_value; last_trade_price := last_trade_price_value; last_trade_quantity := last_trade_quantity_value; last_trade_date_time := last_trade_date_time_value; settle_price_date_time := settle_price_date_time_value; last_message_sequence_id := last_message_sequence_id_value; reserved_2 := reserved_2_value; open_interest_date := open_interest_date_value; is_settle_price_official := is_settle_price_official_value; settlement_price := settlement_price_value; has_previous_day_settlement_price := has_previous_day_settlement_price_value; previous_day_settlement_price := previous_day_settlement_price_value |}, bytes)
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 133.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
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
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSnapshotMessage.

  Module SpotMarketTradeMessage.

    (** This message will be sent only upon trade in spot markets and it will be rendered on spot market channels. *)
    Record t := {
      market_id : N;
      trade_id : N;
      price : N;
      quantity : N;
      transact_date_time : N;
      extra_flags : N;
      delivery_begin_date_time : N;
      delivery_end_date_time : N;
      is_system_priced_leg : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (transact_date_time record < 256 ^ N.of_nat 8)%N /\
      (extra_flags record < 256 ^ N.of_nat 1)%N /\
      (delivery_begin_date_time record < 256 ^ N.of_nat 8)%N /\
      (delivery_end_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (is_system_priced_leg record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (transact_date_time record) ++
      encode_uint 1 (extra_flags record) ++
      encode_uint 8 (delivery_begin_date_time record) ++
      encode_uint 8 (delivery_end_date_time record) ++
      encode_bytes 1 (is_system_priced_leg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (transact_date_time_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (extra_flags_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (delivery_begin_date_time_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (delivery_end_date_time_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (is_system_priced_leg_value, bytes) =>
                                          Some ({| market_id := market_id_value; trade_id := trade_id_value; price := price_value; quantity := quantity_value; transact_date_time := transact_date_time_value; extra_flags := extra_flags_value; delivery_begin_date_time := delivery_begin_date_time_value; delivery_end_date_time := delivery_end_date_time_value; is_system_priced_leg := is_system_priced_leg_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpotMarketTradeMessage.

  Module InvestigatedTradeMessage.

    (** This message is sent when a trade is put under investigation or the investigation is completed. Client can use the market ID and order ID to find and flag the original trade if needed. *)
    Record t := {
      market_id : N;
      trade_id : N;
      price : N;
      quantity : N;
      old_off_market_trade_type : list byte;
      message_date_time : N;
      investigation_status : list byte;
      off_market_trade_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (old_off_market_trade_type record) = 1 /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (investigation_status record) = 1 /\
      Datatypes.length (off_market_trade_type record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (old_off_market_trade_type record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 1 (investigation_status record) ++
      encode_bytes 3 (off_market_trade_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (old_off_market_trade_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (message_date_time_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (investigation_status_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (off_market_trade_type_value, bytes) =>
                                      Some ({| market_id := market_id_value; trade_id := trade_id_value; price := price_value; quantity := quantity_value; old_off_market_trade_type := old_off_market_trade_type_value; message_date_time := message_date_time_value; investigation_status := investigation_status_value; off_market_trade_type := off_market_trade_type_value |}, bytes)
                                  end
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
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InvestigatedTradeMessage.

  Module CancelledTradeMessage.

    (** This message is sent when a trade is cancelled. *)
    Record t := {
      market_id : N;
      trade_id : N;
      price : N;
      quantity : N;
      old_off_market_trade_type : list byte;
      message_date_time : N;
      off_market_trade_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (old_off_market_trade_type record) = 1 /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (off_market_trade_type record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (old_off_market_trade_type record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 3 (off_market_trade_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (old_off_market_trade_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (message_date_time_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (off_market_trade_type_value, bytes) =>
                                  Some ({| market_id := market_id_value; trade_id := trade_id_value; price := price_value; quantity := quantity_value; old_off_market_trade_type := old_off_market_trade_type_value; message_date_time := message_date_time_value; off_market_trade_type := off_market_trade_type_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelledTradeMessage.

  Module MarketStatisticsMessage.

    (** This is usually sent after a trade or cancelled trade message. *)
    Record t := {
      market_id : N;
      volume : N;
      block_volume : N;
      efs_volume : N;
      efp_volume : N;
      high : N;
      low : N;
      vwap : N;
      message_date_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (block_volume record < 256 ^ N.of_nat 4)%N /\
      (efs_volume record < 256 ^ N.of_nat 4)%N /\
      (efp_volume record < 256 ^ N.of_nat 4)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 4 (volume record) ++
      encode_uint 4 (block_volume record) ++
      encode_uint 4 (efs_volume record) ++
      encode_uint 4 (efp_volume record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (message_date_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (volume_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (block_volume_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (efs_volume_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (efp_volume_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (high_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (low_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (vwap_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (message_date_time_value, bytes) =>
                                          Some ({| market_id := market_id_value; volume := volume_value; block_volume := block_volume_value; efs_volume := efs_volume_value; efp_volume := efp_volume_value; high := high_value; low := low_value; vwap := vwap_value; message_date_time := message_date_time_value |}, bytes)
                                      end
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
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MarketStatisticsMessage.

  Module MarketStateChangeMessage.

    (** Market State Change Message *)
    Record t := {
      market_id : N;
      trading_status : list byte;
      message_date_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_status record) = 1 /\
      (message_date_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 1 (trading_status record) ++
      encode_uint 8 (message_date_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_status_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  Some ({| market_id := market_id_value; trading_status := trading_status_value; message_date_time := message_date_time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStateChangeMessage.

  Module SystemTextMessage.

    (** System Text Message *)
    Record t := {
      text_message : list byte;
      message_date_time : N;
      text_message_extra_fld : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (text_message record) = 200 /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (text_message_extra_fld record) = 800.

    Definition encode (record : t) : list byte :=
      encode_bytes 200 (text_message record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 800 (text_message_extra_fld record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 200 bytes with
      | None => None
      | Some (text_message_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_date_time_value, bytes) =>
              match decode_bytes 800 bytes with
              | None => None
              | Some (text_message_extra_fld_value, bytes) =>
                  Some ({| text_message := text_message_value; message_date_time := message_date_time_value; text_message_extra_fld := text_message_extra_fld_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1008.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemTextMessage.

  Module OpenInterestMessage.

    (** Open Interest Message *)
    Record t := {
      market_id : N;
      open_interest : N;
      open_interest_change : N;
      message_date_time : N;
      open_interest_date : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 4)%N /\
      (open_interest_change record < 256 ^ N.of_nat 4)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (open_interest_date record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 4 (open_interest record) ++
      encode_uint 4 (open_interest_change record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 10 (open_interest_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (open_interest_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (open_interest_change_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (message_date_time_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (open_interest_date_value, bytes) =>
                          Some ({| market_id := market_id_value; open_interest := open_interest_value; open_interest_change := open_interest_change_value; message_date_time := message_date_time_value; open_interest_date := open_interest_date_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpenInterestMessage.

  Module OpenPriceMessage.

    (** Open Price Message *)
    Record t := {
      market_id : N;
      open_price : N;
      message_date_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 8 (message_date_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (open_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  Some ({| market_id := market_id_value; open_price := open_price_value; message_date_time := message_date_time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OpenPriceMessage.

  Module ClosePriceMessage.

    (** Close Price Message *)
    Record t := {
      market_id : N;
      close_price : N;
      message_date_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (close_price record < 256 ^ N.of_nat 8)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (close_price record) ++
      encode_uint 8 (message_date_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (close_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  Some ({| market_id := market_id_value; close_price := close_price_value; message_date_time := message_date_time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ClosePriceMessage.

  Module SettlementPriceMessage.

    (** Settlement prices could be official or unofficial. For a given market, the exchange usually sends out unofficial price before the official one. *)
    Record t := {
      market_id : N;
      settlement_price_with_deal_price_precision : N;
      message_date_time : N;
      is_official : list byte;
      valuation_date_time : N;
      settlement_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (settlement_price_with_deal_price_precision record < 256 ^ N.of_nat 8)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (is_official record) = 1 /\
      (valuation_date_time record < 256 ^ N.of_nat 8)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (settlement_price_with_deal_price_precision record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 1 (is_official record) ++
      encode_uint 8 (valuation_date_time record) ++
      encode_uint 8 (settlement_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (settlement_price_with_deal_price_precision_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (is_official_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (valuation_date_time_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (settlement_price_value, bytes) =>
                              Some ({| market_id := market_id_value; settlement_price_with_deal_price_precision := settlement_price_with_deal_price_precision_value; message_date_time := message_date_time_value; is_official := is_official_value; valuation_date_time := valuation_date_time_value; settlement_price := settlement_price_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceMessage.

  Module IndexPricesMessage.

    (** The exchange sends out Marker/Index Prices when there is an update *)
    Record t := {
      market_id : N;
      price : N;
      short_name : list byte;
      published_date_time : N;
      valuation_date_applying_date : list byte;
      endex_status : list byte;
      alt_market_id : N;
      index_price_denominator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (short_name record) = 30 /\
      (published_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (valuation_date_applying_date record) = 10 /\
      Datatypes.length (endex_status record) = 1 /\
      (alt_market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (index_price_denominator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (price record) ++
      encode_bytes 30 (short_name record) ++
      encode_uint 8 (published_date_time record) ++
      encode_bytes 10 (valuation_date_applying_date record) ++
      encode_bytes 1 (endex_status record) ++
      encode_uint 4 (alt_market_id record) ++
      encode_bytes 1 (index_price_denominator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 30 bytes with
              | None => None
              | Some (short_name_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (published_date_time_value, bytes) =>
                      match decode_bytes 10 bytes with
                      | None => None
                      | Some (valuation_date_applying_date_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (endex_status_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (alt_market_id_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (index_price_denominator_value, bytes) =>
                                      Some ({| market_id := market_id_value; price := price_value; short_name := short_name_value; published_date_time := published_date_time_value; valuation_date_applying_date := valuation_date_applying_date_value; endex_status := endex_status_value; alt_market_id := alt_market_id_value; index_price_denominator := index_price_denominator_value |}, bytes)
                                  end
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexPricesMessage.

  Module EndOfDayMarketSummaryMessage.

    (** The message is streamed to client when market is closed and settlement price is available for the current trading day. *)
    Record t := {
      market_id : N;
      volume : N;
      block_volume : N;
      efs_volume : N;
      efp_volume : N;
      opening_price : N;
      high : N;
      low : N;
      vwap : N;
      settlement_price_with_deal_price_precision : N;
      open_interest : N;
      message_date_time : N;
      settlement_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (block_volume record < 256 ^ N.of_nat 4)%N /\
      (efs_volume record < 256 ^ N.of_nat 4)%N /\
      (efp_volume record < 256 ^ N.of_nat 4)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (settlement_price_with_deal_price_precision record < 256 ^ N.of_nat 8)%N /\
      (open_interest record < 256 ^ N.of_nat 4)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 4 (volume record) ++
      encode_uint 4 (block_volume record) ++
      encode_uint 4 (efs_volume record) ++
      encode_uint 4 (efp_volume record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (settlement_price_with_deal_price_precision record) ++
      encode_uint 4 (open_interest record) ++
      encode_uint 8 (message_date_time record) ++
      encode_uint 8 (settlement_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (volume_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (block_volume_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (efs_volume_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (efp_volume_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (opening_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (high_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (low_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (vwap_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (settlement_price_with_deal_price_precision_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (open_interest_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (message_date_time_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (settlement_price_value, bytes) =>
                                                          Some ({| market_id := market_id_value; volume := volume_value; block_volume := block_volume_value; efs_volume := efs_volume_value; efp_volume := efp_volume_value; opening_price := opening_price_value; high := high_value; low := low_value; vwap := vwap_value; settlement_price_with_deal_price_precision := settlement_price_with_deal_price_precision_value; open_interest := open_interest_value; message_date_time := message_date_time_value; settlement_price := settlement_price_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
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
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EndOfDayMarketSummaryMessage.

  Module MarketEventMessage.

    (** End of Day Market Summary Message *)
    Record t := {
      market_id : N;
      event_type : list byte;
      message_date_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_type record) = 1 /\
      (message_date_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 1 (event_type record) ++
      encode_uint 8 (message_date_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  Some ({| market_id := market_id_value; event_type := event_type_value; message_date_time := message_date_time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketEventMessage.

  Module PreOpenPriceIndicatorMessage.

    (** This message contains the estimate of what the opening price could be, based on the orders in the market or previous settlement price. *)
    Record t := {
      market_id : N;
      pre_open_price : N;
      message_date_time : N;
      has_pre_open_volume : list byte;
      pre_open_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (pre_open_price record < 256 ^ N.of_nat 8)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (has_pre_open_volume record) = 1 /\
      (pre_open_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (pre_open_price record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 1 (has_pre_open_volume record) ++
      encode_uint 4 (pre_open_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (pre_open_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (has_pre_open_volume_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (pre_open_volume_value, bytes) =>
                          Some ({| market_id := market_id_value; pre_open_price := pre_open_price_value; message_date_time := message_date_time_value; has_pre_open_volume := has_pre_open_volume_value; pre_open_volume := pre_open_volume_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreOpenPriceIndicatorMessage.

  Module StripInfoMessage.

    (** This message will be sent out if there is strip date change during the trading session. If client does not care about strip date changes, client should ignore these messages. *)
    Record t := {
      old_strip_id : N;
      strip_type : list byte;
      begin_year : N;
      begin_month : N;
      begin_day : N;
      end_year : N;
      end_month : N;
      end_day : N;
      strip_info : list byte;
      strip_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (old_strip_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (strip_type record) = 20 /\
      (begin_year record < 256 ^ N.of_nat 2)%N /\
      (begin_month record < 256 ^ N.of_nat 2)%N /\
      (begin_day record < 256 ^ N.of_nat 2)%N /\
      (end_year record < 256 ^ N.of_nat 2)%N /\
      (end_month record < 256 ^ N.of_nat 2)%N /\
      (end_day record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (strip_info record) = 50 /\
      (strip_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (old_strip_id record) ++
      encode_bytes 20 (strip_type record) ++
      encode_uint 2 (begin_year record) ++
      encode_uint 2 (begin_month record) ++
      encode_uint 2 (begin_day record) ++
      encode_uint 2 (end_year record) ++
      encode_uint 2 (end_month record) ++
      encode_uint 2 (end_day record) ++
      encode_bytes 50 (strip_info record) ++
      encode_uint 4 (strip_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (old_strip_id_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (strip_type_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (begin_year_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (begin_month_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (begin_day_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (end_year_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (end_month_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (end_day_value, bytes) =>
                                      match decode_bytes 50 bytes with
                                      | None => None
                                      | Some (strip_info_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (strip_id_value, bytes) =>
                                              Some ({| old_strip_id := old_strip_id_value; strip_type := strip_type_value; begin_year := begin_year_value; begin_month := begin_month_value; begin_day := begin_day_value; end_year := end_year_value; end_month := end_month_value; end_day := end_day_value; strip_info := strip_info_value; strip_id := strip_id_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StripInfoMessage.

  Module IntervalPriceLimitNotificationMessage.

    (** Interval Price Limit (IPL) might be enabled for certain markets. IPL check is to prevent sudden movements (in both directions) in the market during a short period of time. *)
    Record t := {
      market_id : N;
      ipl_tpl_hold_type : list byte;
      notification_date_time : N;
      is_up : list byte;
      ipl_tpl_hold_duration : N;
      ipl_tpl_up : N;
      ipl_tpl_down : N;
      ipl_tpl_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (ipl_tpl_hold_type record) = 1 /\
      (notification_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (is_up record) = 1 /\
      (ipl_tpl_hold_duration record < 256 ^ N.of_nat 4)%N /\
      (ipl_tpl_up record < 256 ^ N.of_nat 8)%N /\
      (ipl_tpl_down record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (ipl_tpl_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 1 (ipl_tpl_hold_type record) ++
      encode_uint 8 (notification_date_time record) ++
      encode_bytes 1 (is_up record) ++
      encode_uint 4 (ipl_tpl_hold_duration record) ++
      encode_uint 8 (ipl_tpl_up record) ++
      encode_uint 8 (ipl_tpl_down record) ++
      encode_bytes 1 (ipl_tpl_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ipl_tpl_hold_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (notification_date_time_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (is_up_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ipl_tpl_hold_duration_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ipl_tpl_up_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (ipl_tpl_down_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (ipl_tpl_type_value, bytes) =>
                                      Some ({| market_id := market_id_value; ipl_tpl_hold_type := ipl_tpl_hold_type_value; notification_date_time := notification_date_time_value; is_up := is_up_value; ipl_tpl_hold_duration := ipl_tpl_hold_duration_value; ipl_tpl_up := ipl_tpl_up_value; ipl_tpl_down := ipl_tpl_down_value; ipl_tpl_type := ipl_tpl_type_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IntervalPriceLimitNotificationMessage.

  Module NewExpiryMessage.

    (** New Expiry message will be sent out when a new equity market is created during the day. *)
    Record t := {
      market_id : N;
      market_type_id : N;
      order_price_denominator : list byte;
      increment_price : N;
      increment_qty : N;
      lot_size : N;
      market_desc : list byte;
      maturity_year : N;
      maturity_month : N;
      maturity_day : N;
      deal_price_denominator : list byte;
      min_qty : N;
      unit_quantity : N;
      currency : list byte;
      cleared_alias : list byte;
      min_price : N;
      max_price : N;
      product_id : N;
      product_name : list byte;
      hub_id : N;
      hub_alias : list byte;
      strip_id : N;
      strip_name : list byte;
      settle_price_denominator : list byte;
      mic_code : list byte;
      unit_qty_denominator : list byte;
      off_exchange_increment_qty_denominator : list byte;
      off_exchange_increment_qty : N;
      off_exchange_increment_price : N;
      off_exchange_increment_option_price : N;
      contract_symbol : list byte;
      underlying_isin : list byte;
      num_decimals_options_price : list byte;
      hedge_market_id : N;
      settlement_type : list byte;
      gt_allowed : list byte;
      cross_order_supported : list byte;
      unit_of_measure : list byte;
      mifid_regulated_market : list byte;
      screen_last_trade_year : N;
      screen_last_trade_month : N;
      screen_last_trade_day : N;
      old_num_of_cycles : N;
      num_of_cycles : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (market_type_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_price_denominator record) = 1 /\
      (increment_price record < 256 ^ N.of_nat 4)%N /\
      (increment_qty record < 256 ^ N.of_nat 4)%N /\
      (lot_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_desc record) = 120 /\
      (maturity_year record < 256 ^ N.of_nat 2)%N /\
      (maturity_month record < 256 ^ N.of_nat 2)%N /\
      (maturity_day record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (deal_price_denominator record) = 1 /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      (unit_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 20 /\
      Datatypes.length (cleared_alias record) = 15 /\
      (min_price record < 256 ^ N.of_nat 8)%N /\
      (max_price record < 256 ^ N.of_nat 8)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (product_name record) = 62 /\
      (hub_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (hub_alias record) = 80 /\
      (strip_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (strip_name record) = 39 /\
      Datatypes.length (settle_price_denominator record) = 1 /\
      Datatypes.length (mic_code record) = 4 /\
      Datatypes.length (unit_qty_denominator record) = 1 /\
      Datatypes.length (off_exchange_increment_qty_denominator record) = 1 /\
      (off_exchange_increment_qty record < 256 ^ N.of_nat 4)%N /\
      (off_exchange_increment_price record < 256 ^ N.of_nat 4)%N /\
      (off_exchange_increment_option_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (contract_symbol record) = 35 /\
      Datatypes.length (underlying_isin record) = 12 /\
      Datatypes.length (num_decimals_options_price record) = 1 /\
      (hedge_market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (gt_allowed record) = 1 /\
      Datatypes.length (cross_order_supported record) = 1 /\
      Datatypes.length (unit_of_measure record) = 30 /\
      Datatypes.length (mifid_regulated_market record) = 1 /\
      (screen_last_trade_year record < 256 ^ N.of_nat 2)%N /\
      (screen_last_trade_month record < 256 ^ N.of_nat 2)%N /\
      (screen_last_trade_day record < 256 ^ N.of_nat 2)%N /\
      (old_num_of_cycles record < 256 ^ N.of_nat 2)%N /\
      (num_of_cycles record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 2 (market_type_id record) ++
      encode_bytes 1 (order_price_denominator record) ++
      encode_uint 4 (increment_price record) ++
      encode_uint 4 (increment_qty record) ++
      encode_uint 4 (lot_size record) ++
      encode_bytes 120 (market_desc record) ++
      encode_uint 2 (maturity_year record) ++
      encode_uint 2 (maturity_month record) ++
      encode_uint 2 (maturity_day record) ++
      encode_bytes 1 (deal_price_denominator record) ++
      encode_uint 4 (min_qty record) ++
      encode_uint 4 (unit_quantity record) ++
      encode_bytes 20 (currency record) ++
      encode_bytes 15 (cleared_alias record) ++
      encode_uint 8 (min_price record) ++
      encode_uint 8 (max_price record) ++
      encode_uint 4 (product_id record) ++
      encode_bytes 62 (product_name record) ++
      encode_uint 4 (hub_id record) ++
      encode_bytes 80 (hub_alias record) ++
      encode_uint 4 (strip_id record) ++
      encode_bytes 39 (strip_name record) ++
      encode_bytes 1 (settle_price_denominator record) ++
      encode_bytes 4 (mic_code record) ++
      encode_bytes 1 (unit_qty_denominator record) ++
      encode_bytes 1 (off_exchange_increment_qty_denominator record) ++
      encode_uint 4 (off_exchange_increment_qty record) ++
      encode_uint 4 (off_exchange_increment_price record) ++
      encode_uint 4 (off_exchange_increment_option_price record) ++
      encode_bytes 35 (contract_symbol record) ++
      encode_bytes 12 (underlying_isin record) ++
      encode_bytes 1 (num_decimals_options_price record) ++
      encode_uint 4 (hedge_market_id record) ++
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (gt_allowed record) ++
      encode_bytes 1 (cross_order_supported record) ++
      encode_bytes 30 (unit_of_measure record) ++
      encode_bytes 1 (mifid_regulated_market record) ++
      encode_uint 2 (screen_last_trade_year record) ++
      encode_uint 2 (screen_last_trade_month record) ++
      encode_uint 2 (screen_last_trade_day record) ++
      encode_uint 2 (old_num_of_cycles record) ++
      encode_uint 4 (num_of_cycles record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (market_type_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_price_denominator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (increment_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (increment_qty_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (lot_size_value, bytes) =>
                              match decode_bytes 120 bytes with
                              | None => None
                              | Some (market_desc_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (maturity_year_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (maturity_month_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (maturity_day_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (deal_price_denominator_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (min_qty_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (unit_quantity_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (currency_value, bytes) =>
                                                              match decode_bytes 15 bytes with
                                                              | None => None
                                                              | Some (cleared_alias_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (min_price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (max_price_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (product_id_value, bytes) =>
                                                                              match decode_bytes 62 bytes with
                                                                              | None => None
                                                                              | Some (product_name_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (hub_id_value, bytes) =>
                                                                                      match decode_bytes 80 bytes with
                                                                                      | None => None
                                                                                      | Some (hub_alias_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (strip_id_value, bytes) =>
                                                                                              match decode_bytes 39 bytes with
                                                                                              | None => None
                                                                                              | Some (strip_name_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (settle_price_denominator_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (mic_code_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (unit_qty_denominator_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (off_exchange_increment_qty_denominator_value, bytes) =>
                                                                                                                  match decode_uint 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (off_exchange_increment_qty_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (off_exchange_increment_price_value, bytes) =>
                                                                                                                          match decode_uint 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (off_exchange_increment_option_price_value, bytes) =>
                                                                                                                              match decode_bytes 35 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (contract_symbol_value, bytes) =>
                                                                                                                                  match decode_bytes 12 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (underlying_isin_value, bytes) =>
                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (num_decimals_options_price_value, bytes) =>
                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (hedge_market_id_value, bytes) =>
                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (settlement_type_value, bytes) =>
                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (gt_allowed_value, bytes) =>
                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (cross_order_supported_value, bytes) =>
                                                                                                                                                          match decode_bytes 30 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (unit_of_measure_value, bytes) =>
                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (mifid_regulated_market_value, bytes) =>
                                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (screen_last_trade_year_value, bytes) =>
                                                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (screen_last_trade_month_value, bytes) =>
                                                                                                                                                                          match decode_uint 2 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (screen_last_trade_day_value, bytes) =>
                                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (old_num_of_cycles_value, bytes) =>
                                                                                                                                                                                  match decode_uint 4 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (num_of_cycles_value, bytes) =>
                                                                                                                                                                                      Some ({| market_id := market_id_value; market_type_id := market_type_id_value; order_price_denominator := order_price_denominator_value; increment_price := increment_price_value; increment_qty := increment_qty_value; lot_size := lot_size_value; market_desc := market_desc_value; maturity_year := maturity_year_value; maturity_month := maturity_month_value; maturity_day := maturity_day_value; deal_price_denominator := deal_price_denominator_value; min_qty := min_qty_value; unit_quantity := unit_quantity_value; currency := currency_value; cleared_alias := cleared_alias_value; min_price := min_price_value; max_price := max_price_value; product_id := product_id_value; product_name := product_name_value; hub_id := hub_id_value; hub_alias := hub_alias_value; strip_id := strip_id_value; strip_name := strip_name_value; settle_price_denominator := settle_price_denominator_value; mic_code := mic_code_value; unit_qty_denominator := unit_qty_denominator_value; off_exchange_increment_qty_denominator := off_exchange_increment_qty_denominator_value; off_exchange_increment_qty := off_exchange_increment_qty_value; off_exchange_increment_price := off_exchange_increment_price_value; off_exchange_increment_option_price := off_exchange_increment_option_price_value; contract_symbol := contract_symbol_value; underlying_isin := underlying_isin_value; num_decimals_options_price := num_decimals_options_price_value; hedge_market_id := hedge_market_id_value; settlement_type := settlement_type_value; gt_allowed := gt_allowed_value; cross_order_supported := cross_order_supported_value; unit_of_measure := unit_of_measure_value; mifid_regulated_market := mifid_regulated_market_value; screen_last_trade_year := screen_last_trade_year_value; screen_last_trade_month := screen_last_trade_month_value; screen_last_trade_day := screen_last_trade_day_value; old_num_of_cycles := old_num_of_cycles_value; num_of_cycles := num_of_cycles_value |}, bytes)
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 515.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 bound_43]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewExpiryMessage.

  Module NewOptionsMarketDefinitionMessage.

    (** New Options Market Definition messages will be sent out when new options markets are created. *)
    Record t := {
      market_id : N;
      underlying_market_id : N;
      futures_contract_symbol : list byte;
      trading_status : list byte;
      order_price_denominator : list byte;
      increment_qty : N;
      lot_size : N;
      market_desc : list byte;
      option_type : list byte;
      strike_price : N;
      deal_price_denominator : list byte;
      min_qty : N;
      currency : list byte;
      num_decimals_strike_price : list byte;
      min_options_price : N;
      max_options_price : N;
      increment_premium_price : N;
      options_expiration_year : N;
      options_expiration_month : N;
      options_expiration_day : N;
      options_style : list byte;
      options_expiration_type : list byte;
      hedge_market_id : N;
      settle_price_denominator : list byte;
      unit_qty_denominator : list byte;
      tick_value : N;
      flex_allowed : list byte;
      settlement_type : list byte;
      is_block_only : list byte;
      gt_allowed : list byte;
      cross_order_supported : list byte;
      guaranteed_cross_supported : list byte;
      unit_of_measure : list byte;
      mifid_regulated_market : list byte;
      screen_last_trade_year : N;
      screen_last_trade_month : N;
      screen_last_trade_day : N;
      is_tradable : list byte;
      old_num_of_cycles : N;
      market_type_id : N;
      num_of_cycles : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (underlying_market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (futures_contract_symbol record) = 70 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (order_price_denominator record) = 1 /\
      (increment_qty record < 256 ^ N.of_nat 4)%N /\
      (lot_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (market_desc record) = 120 /\
      Datatypes.length (option_type record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (deal_price_denominator record) = 1 /\
      (min_qty record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (currency record) = 20 /\
      Datatypes.length (num_decimals_strike_price record) = 1 /\
      (min_options_price record < 256 ^ N.of_nat 8)%N /\
      (max_options_price record < 256 ^ N.of_nat 8)%N /\
      (increment_premium_price record < 256 ^ N.of_nat 4)%N /\
      (options_expiration_year record < 256 ^ N.of_nat 2)%N /\
      (options_expiration_month record < 256 ^ N.of_nat 2)%N /\
      (options_expiration_day record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (options_style record) = 1 /\
      Datatypes.length (options_expiration_type record) = 1 /\
      (hedge_market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settle_price_denominator record) = 1 /\
      Datatypes.length (unit_qty_denominator record) = 1 /\
      (tick_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (flex_allowed record) = 1 /\
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (is_block_only record) = 1 /\
      Datatypes.length (gt_allowed record) = 1 /\
      Datatypes.length (cross_order_supported record) = 1 /\
      Datatypes.length (guaranteed_cross_supported record) = 1 /\
      Datatypes.length (unit_of_measure record) = 30 /\
      Datatypes.length (mifid_regulated_market record) = 1 /\
      (screen_last_trade_year record < 256 ^ N.of_nat 2)%N /\
      (screen_last_trade_month record < 256 ^ N.of_nat 2)%N /\
      (screen_last_trade_day record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (is_tradable record) = 1 /\
      (old_num_of_cycles record < 256 ^ N.of_nat 2)%N /\
      (market_type_id record < 256 ^ N.of_nat 2)%N /\
      (num_of_cycles record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 4 (underlying_market_id record) ++
      encode_bytes 70 (futures_contract_symbol record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 1 (order_price_denominator record) ++
      encode_uint 4 (increment_qty record) ++
      encode_uint 4 (lot_size record) ++
      encode_bytes 120 (market_desc record) ++
      encode_bytes 1 (option_type record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (deal_price_denominator record) ++
      encode_uint 4 (min_qty record) ++
      encode_bytes 20 (currency record) ++
      encode_bytes 1 (num_decimals_strike_price record) ++
      encode_uint 8 (min_options_price record) ++
      encode_uint 8 (max_options_price record) ++
      encode_uint 4 (increment_premium_price record) ++
      encode_uint 2 (options_expiration_year record) ++
      encode_uint 2 (options_expiration_month record) ++
      encode_uint 2 (options_expiration_day record) ++
      encode_bytes 1 (options_style record) ++
      encode_bytes 1 (options_expiration_type record) ++
      encode_uint 4 (hedge_market_id record) ++
      encode_bytes 1 (settle_price_denominator record) ++
      encode_bytes 1 (unit_qty_denominator record) ++
      encode_uint 8 (tick_value record) ++
      encode_bytes 1 (flex_allowed record) ++
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (is_block_only record) ++
      encode_bytes 1 (gt_allowed record) ++
      encode_bytes 1 (cross_order_supported record) ++
      encode_bytes 1 (guaranteed_cross_supported record) ++
      encode_bytes 30 (unit_of_measure record) ++
      encode_bytes 1 (mifid_regulated_market record) ++
      encode_uint 2 (screen_last_trade_year record) ++
      encode_uint 2 (screen_last_trade_month record) ++
      encode_uint 2 (screen_last_trade_day record) ++
      encode_bytes 1 (is_tradable record) ++
      encode_uint 2 (old_num_of_cycles record) ++
      encode_uint 2 (market_type_id record) ++
      encode_uint 4 (num_of_cycles record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (underlying_market_id_value, bytes) =>
              match decode_bytes 70 bytes with
              | None => None
              | Some (futures_contract_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (order_price_denominator_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (increment_qty_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (lot_size_value, bytes) =>
                                  match decode_bytes 120 bytes with
                                  | None => None
                                  | Some (market_desc_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (option_type_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (strike_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (deal_price_denominator_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (min_qty_value, bytes) =>
                                                      match decode_bytes 20 bytes with
                                                      | None => None
                                                      | Some (currency_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (num_decimals_strike_price_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (min_options_price_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (max_options_price_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (increment_premium_price_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (options_expiration_year_value, bytes) =>
                                                                              match decode_uint 2 bytes with
                                                                              | None => None
                                                                              | Some (options_expiration_month_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (options_expiration_day_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (options_style_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (options_expiration_type_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (hedge_market_id_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (settle_price_denominator_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (unit_qty_denominator_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (tick_value_value, bytes) =>
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (flex_allowed_value, bytes) =>
                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (settlement_type_value, bytes) =>
                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (is_block_only_value, bytes) =>
                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (gt_allowed_value, bytes) =>
                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (cross_order_supported_value, bytes) =>
                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (guaranteed_cross_supported_value, bytes) =>
                                                                                                                                      match decode_bytes 30 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (unit_of_measure_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (mifid_regulated_market_value, bytes) =>
                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (screen_last_trade_year_value, bytes) =>
                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (screen_last_trade_month_value, bytes) =>
                                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (screen_last_trade_day_value, bytes) =>
                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (is_tradable_value, bytes) =>
                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (old_num_of_cycles_value, bytes) =>
                                                                                                                                                                  match decode_uint 2 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (market_type_id_value, bytes) =>
                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (num_of_cycles_value, bytes) =>
                                                                                                                                                                          Some ({| market_id := market_id_value; underlying_market_id := underlying_market_id_value; futures_contract_symbol := futures_contract_symbol_value; trading_status := trading_status_value; order_price_denominator := order_price_denominator_value; increment_qty := increment_qty_value; lot_size := lot_size_value; market_desc := market_desc_value; option_type := option_type_value; strike_price := strike_price_value; deal_price_denominator := deal_price_denominator_value; min_qty := min_qty_value; currency := currency_value; num_decimals_strike_price := num_decimals_strike_price_value; min_options_price := min_options_price_value; max_options_price := max_options_price_value; increment_premium_price := increment_premium_price_value; options_expiration_year := options_expiration_year_value; options_expiration_month := options_expiration_month_value; options_expiration_day := options_expiration_day_value; options_style := options_style_value; options_expiration_type := options_expiration_type_value; hedge_market_id := hedge_market_id_value; settle_price_denominator := settle_price_denominator_value; unit_qty_denominator := unit_qty_denominator_value; tick_value := tick_value_value; flex_allowed := flex_allowed_value; settlement_type := settlement_type_value; is_block_only := is_block_only_value; gt_allowed := gt_allowed_value; cross_order_supported := cross_order_supported_value; guaranteed_cross_supported := guaranteed_cross_supported_value; unit_of_measure := unit_of_measure_value; mifid_regulated_market := mifid_regulated_market_value; screen_last_trade_year := screen_last_trade_year_value; screen_last_trade_month := screen_last_trade_month_value; screen_last_trade_day := screen_last_trade_day_value; is_tradable := is_tradable_value; old_num_of_cycles := old_num_of_cycles_value; market_type_id := market_type_id_value; num_of_cycles := num_of_cycles_value |}, bytes)
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 337.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 bound_40]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      rewrite decode_encode_uint by exact bound_39.
      rewrite decode_encode_uint by exact bound_40.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewOptionsMarketDefinitionMessage.

  Module OptionOpenInterestMessage.

    (** Option Open Interest Message *)
    Record t := {
      market_id : N;
      open_interest : N;
      message_date_time : N;
      open_interest_date : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 4)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (open_interest_date record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 4 (open_interest record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 10 (open_interest_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (open_interest_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  match decode_bytes 10 bytes with
                  | None => None
                  | Some (open_interest_date_value, bytes) =>
                      Some ({| market_id := market_id_value; open_interest := open_interest_value; message_date_time := message_date_time_value; open_interest_date := open_interest_date_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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

  End OptionOpenInterestMessage.

  Module OptionSettlementPriceMessage.

    (** Option settlement prices could be official or unofficial. For a given market, the exchange usually sends out unofficial price before the official one. *)
    Record t := {
      market_id : N;
      settlement_price_with_deal_price_precision : N;
      message_date_time : N;
      is_official : list byte;
      valuation_date_time : N;
      volatility : N;
      settlement_price : N;
      delta : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (settlement_price_with_deal_price_precision record < 256 ^ N.of_nat 8)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (is_official record) = 1 /\
      (valuation_date_time record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      (delta record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (settlement_price_with_deal_price_precision record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 1 (is_official record) ++
      encode_uint 8 (valuation_date_time record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (settlement_price record) ++
      encode_uint 8 (delta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (settlement_price_with_deal_price_precision_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (is_official_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (valuation_date_time_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (volatility_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (settlement_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (delta_value, bytes) =>
                                      Some ({| market_id := market_id_value; settlement_price_with_deal_price_precision := settlement_price_with_deal_price_precision_value; message_date_time := message_date_time_value; is_official := is_official_value; valuation_date_time := valuation_date_time_value; volatility := volatility_value; settlement_price := settlement_price_value; delta := delta_value |}, bytes)
                                  end
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

  End OptionSettlementPriceMessage.

  Module MarketSnapshotOrderMessage.

    (** This message is for orders in snapshot only. It is different from the order message for incremental updates. *)
    Record t := {
      market_id : N;
      order_id : N;
      order_sequence_id : N;
      side : list byte;
      price : N;
      quantity : N;
      is_implied : list byte;
      is_rfq : list byte;
      order_entry_date_time : N;
      sequence_within_millis : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_sequence_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (is_implied record) = 1 /\
      Datatypes.length (is_rfq record) = 1 /\
      (order_entry_date_time record < 256 ^ N.of_nat 8)%N /\
      (sequence_within_millis record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (order_sequence_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (is_implied record) ++
      encode_bytes 1 (is_rfq record) ++
      encode_uint 8 (order_entry_date_time record) ++
      encode_uint 4 (sequence_within_millis record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (order_sequence_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (is_implied_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (is_rfq_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (order_entry_date_time_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (sequence_within_millis_value, bytes) =>
                                              Some ({| market_id := market_id_value; order_id := order_id_value; order_sequence_id := order_sequence_id_value; side := side_value; price := price_value; quantity := quantity_value; is_implied := is_implied_value; is_rfq := is_rfq_value; order_entry_date_time := order_entry_date_time_value; sequence_within_millis := sequence_within_millis_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSnapshotOrderMessage.

  Module DeleteOrderMessage.

    (** Upon receipt of this message, client should remove the order from its local book. *)
    Record t := {
      market_id : N;
      order_id : N;
      message_date_time : N;
      sequence_within_millis : N;
      request_trading_engine_received_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      (sequence_within_millis record < 256 ^ N.of_nat 4)%N /\
      (request_trading_engine_received_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (message_date_time record) ++
      encode_uint 4 (sequence_within_millis record) ++
      encode_uint 8 (request_trading_engine_received_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_within_millis_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (request_trading_engine_received_timestamp_value, bytes) =>
                          Some ({| market_id := market_id_value; order_id := order_id_value; message_date_time := message_date_time_value; sequence_within_millis := sequence_within_millis_value; request_trading_engine_received_timestamp := request_trading_engine_received_timestamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End DeleteOrderMessage.

  Module MessageBundleMarker.

    (** This message indicates where a bundle of messages starts or ends. *)
    Record t := {
      start_or_end : list byte;
      trade_transaction_id : N;
      is_transaction_end : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (start_or_end record) = 1 /\
      (trade_transaction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (is_transaction_end record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (start_or_end record) ++
      encode_uint 8 (trade_transaction_id record) ++
      encode_bytes 1 (is_transaction_end record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (start_or_end_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_transaction_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (is_transaction_end_value, bytes) =>
                  Some ({| start_or_end := start_or_end_value; trade_transaction_id := trade_transaction_id_value; is_transaction_end := is_transaction_end_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageBundleMarker.

  Module FixingTransitionMessage.

    (** This message supports ICE Benchmark Administration’s (IBA) electronic Gold Auction and it is disseminated when there is a transition of the fixing market. *)
    Record t := {
      market_id : N;
      fixing_status : list byte;
      auction_end_time : N;
      threshold_imbalance_qty : N;
      message_date_time : N;
      num_decimals_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (fixing_status record) = 1 /\
      (auction_end_time record < 256 ^ N.of_nat 8)%N /\
      (threshold_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      (num_decimals_quantity record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 1 (fixing_status record) ++
      encode_uint 8 (auction_end_time record) ++
      encode_uint 4 (threshold_imbalance_qty record) ++
      encode_uint 8 (message_date_time record) ++
      encode_uint 1 (num_decimals_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixing_status_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (auction_end_time_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (threshold_imbalance_qty_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (message_date_time_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (num_decimals_quantity_value, bytes) =>
                              Some ({| market_id := market_id_value; fixing_status := fixing_status_value; auction_end_time := auction_end_time_value; threshold_imbalance_qty := threshold_imbalance_qty_value; message_date_time := message_date_time_value; num_decimals_quantity := num_decimals_quantity_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixingTransitionMessage.

  Module FixingLockdownMessage.

    (** This message supports ICE Benchmark Administration’s (IBA) electronic Gold Auction and it is disseminated when there is a transition of the fixing market. *)
    Record t := {
      market_id : N;
      auction_date : list byte;
      message_date_time : N;
      description : list byte;
      round : N;
      agg_bid_qty : N;
      agg_offer_qty : N;
      usd_price : N;
      is_balanced : list byte;
      is_final : list byte;
      gbp_price : N;
      eur_price : N;
      num_decimals_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_date record) = 10 /\
      (message_date_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (description record) = 20 /\
      (round record < 256 ^ N.of_nat 2)%N /\
      (agg_bid_qty record < 256 ^ N.of_nat 4)%N /\
      (agg_offer_qty record < 256 ^ N.of_nat 4)%N /\
      (usd_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (is_balanced record) = 1 /\
      Datatypes.length (is_final record) = 1 /\
      (gbp_price record < 256 ^ N.of_nat 8)%N /\
      (eur_price record < 256 ^ N.of_nat 8)%N /\
      (num_decimals_quantity record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 10 (auction_date record) ++
      encode_uint 8 (message_date_time record) ++
      encode_bytes 20 (description record) ++
      encode_uint 2 (round record) ++
      encode_uint 4 (agg_bid_qty record) ++
      encode_uint 4 (agg_offer_qty record) ++
      encode_uint 8 (usd_price record) ++
      encode_bytes 1 (is_balanced record) ++
      encode_bytes 1 (is_final record) ++
      encode_uint 8 (gbp_price record) ++
      encode_uint 8 (eur_price record) ++
      encode_uint 1 (num_decimals_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (auction_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (message_date_time_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (description_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (round_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (agg_bid_qty_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (agg_offer_qty_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (usd_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (is_balanced_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (is_final_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (gbp_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (eur_price_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (num_decimals_quantity_value, bytes) =>
                                                          Some ({| market_id := market_id_value; auction_date := auction_date_value; message_date_time := message_date_time_value; description := description_value; round := round_value; agg_bid_qty := agg_bid_qty_value; agg_offer_qty := agg_offer_qty_value; usd_price := usd_price_value; is_balanced := is_balanced_value; is_final := is_final_value; gbp_price := gbp_price_value; eur_price := eur_price_value; num_decimals_quantity := num_decimals_quantity_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 79.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixingLockdownMessage.

  Module FixingIndicativePriceMessage.

    (** This message supports ICE Benchmark Administration’s (IBA) electronic Gold and Silver Auction and is disseminated at the end of the final auction when the final price is published *)
    Record t := {
      market_id : N;
      iba_currency : list byte;
      price : N;
      price_in_gram : N;
      num_decimals_price : N;
      num_decimals_price_in_gram : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (iba_currency record) = 3 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (price_in_gram record < 256 ^ N.of_nat 8)%N /\
      (num_decimals_price record < 256 ^ N.of_nat 1)%N /\
      (num_decimals_price_in_gram record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 3 (iba_currency record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (price_in_gram record) ++
      encode_uint 1 (num_decimals_price record) ++
      encode_uint 1 (num_decimals_price_in_gram record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 3 bytes with
          | None => None
          | Some (iba_currency_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_in_gram_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (num_decimals_price_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (num_decimals_price_in_gram_value, bytes) =>
                              Some ({| market_id := market_id_value; iba_currency := iba_currency_value; price := price_value; price_in_gram := price_in_gram_value; num_decimals_price := num_decimals_price_value; num_decimals_price_in_gram := num_decimals_price_in_gram_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixingIndicativePriceMessage.

  Module MarketSnapshotPriceLevelMessage.

    (** This message is for price level in snapshot only. *)
    Record t := {
      market_id : N;
      side : list byte;
      price_level_position : N;
      price : N;
      quantity : N;
      order_count : N;
      implied_quantity : N;
      implied_order_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price_level_position record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_count record < 256 ^ N.of_nat 2)%N /\
      (implied_quantity record < 256 ^ N.of_nat 4)%N /\
      (implied_order_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (price_level_position record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 2 (order_count record) ++
      encode_uint 4 (implied_quantity record) ++
      encode_uint 2 (implied_order_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (price_level_position_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (order_count_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (implied_quantity_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (implied_order_count_value, bytes) =>
                                      Some ({| market_id := market_id_value; side := side_value; price_level_position := price_level_position_value; price := price_value; quantity := quantity_value; order_count := order_count_value; implied_quantity := implied_quantity_value; implied_order_count := implied_order_count_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketSnapshotPriceLevelMessage.

  Module AddPriceLevelMessage.

    (** Upon receipt of this message, client should add/insert a price level at the specified position in the book for the given market, and push down the price levels that were previously at or below that position. *)
    Record t := {
      market_id : N;
      side : list byte;
      price_level_position : N;
      price : N;
      quantity : N;
      order_count : N;
      implied_quantity : N;
      implied_order_count : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price_level_position record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_count record < 256 ^ N.of_nat 2)%N /\
      (implied_quantity record < 256 ^ N.of_nat 4)%N /\
      (implied_order_count record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (price_level_position record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 2 (order_count record) ++
      encode_uint 4 (implied_quantity record) ++
      encode_uint 2 (implied_order_count record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (price_level_position_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (order_count_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (implied_quantity_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (implied_order_count_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (timestamp_value, bytes) =>
                                          Some ({| market_id := market_id_value; side := side_value; price_level_position := price_level_position_value; price := price_value; quantity := quantity_value; order_count := order_count_value; implied_quantity := implied_quantity_value; implied_order_count := implied_order_count_value; timestamp := timestamp_value |}, bytes)
                                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddPriceLevelMessage.

  Module ChangePriceLevelMessage.

    (** Upon receipt of this message, client should update the price level at the specified position in its book for the given market. *)
    Record t := {
      market_id : N;
      side : list byte;
      price_level_position : N;
      price : N;
      quantity : N;
      order_count : N;
      implied_quantity : N;
      implied_order_count : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price_level_position record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (order_count record < 256 ^ N.of_nat 2)%N /\
      (implied_quantity record < 256 ^ N.of_nat 4)%N /\
      (implied_order_count record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (price_level_position record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 2 (order_count record) ++
      encode_uint 4 (implied_quantity record) ++
      encode_uint 2 (implied_order_count record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (price_level_position_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (order_count_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (implied_quantity_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (implied_order_count_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (timestamp_value, bytes) =>
                                          Some ({| market_id := market_id_value; side := side_value; price_level_position := price_level_position_value; price := price_value; quantity := quantity_value; order_count := order_count_value; implied_quantity := implied_quantity_value; implied_order_count := implied_order_count_value; timestamp := timestamp_value |}, bytes)
                                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ChangePriceLevelMessage.

  Module DeletePriceLevelMessage.

    (** Upon receipt of this message, client should remove the price level at the specified position in its book for the given market. *)
    Record t := {
      market_id : N;
      side : list byte;
      price_level_position : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (price_level_position record < 256 ^ N.of_nat 1)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (price_level_position record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (price_level_position_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_value, bytes) =>
                      Some ({| market_id := market_id_value; side := side_value; price_level_position := price_level_position_value; timestamp := timestamp_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DeletePriceLevelMessage.

  Module RfqMessage.

    (** Request for Quote Message. *)
    Record t := {
      market_id : N;
      message_timestamp : N;
      rfq_system_id : N;
      market_type_id : N;
      underlying_market_id : N;
      quantity : N;
      side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_id record < 256 ^ N.of_nat 4)%N /\
      (message_timestamp record < 256 ^ N.of_nat 8)%N /\
      (rfq_system_id record < 256 ^ N.of_nat 8)%N /\
      (market_type_id record < 256 ^ N.of_nat 2)%N /\
      (underlying_market_id record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_id record) ++
      encode_uint 8 (message_timestamp record) ++
      encode_uint 8 (rfq_system_id record) ++
      encode_uint 2 (market_type_id record) ++
      encode_uint 4 (underlying_market_id record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (message_timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (rfq_system_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_type_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (underlying_market_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  Some ({| market_id := market_id_value; message_timestamp := message_timestamp_value; rfq_system_id := rfq_system_id_value; market_type_id := market_type_id_value; underlying_market_id := underlying_market_id_value; quantity := quantity_value; side := side_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RfqMessage.

End IceFuturesMdfV1151.
