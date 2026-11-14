From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Investors Exchange Market Data

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
      - a block whose stated length holds more than its fields
      - a run counted by a field
      - a field present only on a condition

    License: MIT No Attribution
  *)

Module IexOptionsMarketDataV103.

  Module MessageHeader.

    (** Iex Options Sbe message header — message identifiers and length of message root *)
    Record t := {
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (schema_id record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (block_length record) ++
      encode_uint_le 2 (template_id record) ++
      encode_uint_le 2 (schema_id record) ++
      encode_uint_le 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (template_id_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (schema_id_value, bytes) =>
                  match decode_uint_le 2 bytes with
                  | None => None
                  | Some (version_value, bytes) =>
                      Some ({| block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module UnderlyingRefDataMessage.

    (** UnderlyingRefDataMessage *)
    Record t := {
      time : N;
      underlying_id : N;
      underlying_symbol : list byte;
      exchange_code : list byte;
      mpv_group : N;
      close_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (underlying_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 16 /\
      Datatypes.length (exchange_code record) = 1 /\
      (mpv_group record < 256 ^ N.of_nat 1)%N /\
      (close_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (underlying_id record) ++
      encode_bytes 16 (underlying_symbol record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_uint 1 (mpv_group record) ++
      encode_uint 1 (close_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (underlying_id_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (exchange_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (mpv_group_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (close_indicator_value, bytes) =>
                              Some ({| time := time_value; underlying_id := underlying_id_value; underlying_symbol := underlying_symbol_value; exchange_code := exchange_code_value; mpv_group := mpv_group_value; close_indicator := close_indicator_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingRefDataMessage.

  Module SymbolMappingMessage.

    (** SymbolMappingMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      osi_symbol : list byte;
      trading_ring : N;
      closing_only_series : N;
      underlying_id : N;
      maturity_date : list byte;
      option_type : N;
      strike_price : N;
      orp_enablement : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (osi_symbol record) = 32 /\
      (trading_ring record < 256 ^ N.of_nat 1)%N /\
      (closing_only_series record < 256 ^ N.of_nat 1)%N /\
      (underlying_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (maturity_date record) = 8 /\
      (option_type record < 256 ^ N.of_nat 1)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (orp_enablement record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_bytes 32 (osi_symbol record) ++
      encode_uint 1 (trading_ring record) ++
      encode_uint 1 (closing_only_series record) ++
      encode_uint_le 4 (underlying_id record) ++
      encode_bytes 8 (maturity_date record) ++
      encode_uint 1 (option_type record) ++
      encode_uint_le 8 (strike_price record) ++
      encode_uint 1 (orp_enablement record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (osi_symbol_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trading_ring_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (closing_only_series_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (underlying_id_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (maturity_date_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (option_type_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (strike_price_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (orp_enablement_value, bytes) =>
                                              Some ({| time := time_value; instrument_id := instrument_id_value; osi_symbol := osi_symbol_value; trading_ring := trading_ring_value; closing_only_series := closing_only_series_value; underlying_id := underlying_id_value; maturity_date := maturity_date_value; option_type := option_type_value; strike_price := strike_price_value; orp_enablement := orp_enablement_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolMappingMessage.

  Module InstrumentClearMessage.

    (** InstrumentClearMessage *)
    Record t := {
      time : N;
      instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              Some ({| time := time_value; instrument_id := instrument_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrumentClearMessage.

  Module TradingStatusMessage.

    (** TradingStatusMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      trading_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trading_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (trading_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  Some ({| time := time_value; instrument_id := instrument_id_value; trading_status := trading_status_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TradingStatusMessage.

  Module OptionsAuctionSummaryMessage.

    (** OptionsAuctionSummaryMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      auction_summary_type : N;
      price : N;
      contracts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (auction_summary_type record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (contracts record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (auction_summary_type record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (contracts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (auction_summary_type_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (contracts_value, bytes) =>
                          Some ({| time := time_value; instrument_id := instrument_id_value; auction_summary_type := auction_summary_type_value; price := price_value; contracts := contracts_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OptionsAuctionSummaryMessage.

  Module OptionsAuctionWidthUpdateMessage.

    (** OptionsAuctionWidthUpdateMessage *)
    Record t := {
      time : N;
      underlying_id : N;
      quote_relief_multiplier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (underlying_id record < 256 ^ N.of_nat 4)%N /\
      (quote_relief_multiplier record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (underlying_id record) ++
      encode_uint 1 (quote_relief_multiplier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (underlying_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (quote_relief_multiplier_value, bytes) =>
                  Some ({| time := time_value; underlying_id := underlying_id_value; quote_relief_multiplier := quote_relief_multiplier_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OptionsAuctionWidthUpdateMessage.

  Module LiquidityEventNotificationMessage.

    (** LiquidityEventNotificationMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      event_id : N;
      liquidity_event_type : N;
      side : N;
      price : N;
      contracts : N;
      capacity : N;
      participant_id : list byte;
      event_end_offset : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (event_id record < 256 ^ N.of_nat 4)%N /\
      (liquidity_event_type record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (capacity record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (participant_id record) = 4 /\
      (event_end_offset record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 4 (event_id record) ++
      encode_uint 1 (liquidity_event_type record) ++
      encode_uint 1 (side record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (contracts record) ++
      encode_uint 1 (capacity record) ++
      encode_bytes 4 (participant_id record) ++
      encode_uint_le 4 (event_end_offset record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (event_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (liquidity_event_type_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (contracts_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (capacity_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (participant_id_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (event_end_offset_value, bytes) =>
                                              Some ({| time := time_value; instrument_id := instrument_id_value; event_id := event_id_value; liquidity_event_type := liquidity_event_type_value; side := side_value; price := price_value; contracts := contracts_value; capacity := capacity_value; participant_id := participant_id_value; event_end_offset := event_end_offset_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LiquidityEventNotificationMessage.

  Module LiquidityEventExecutionMessage.

    (** LiquidityEventExecutionMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      event_id : N;
      trade_id : N;
      price : N;
      contracts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (event_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (contracts record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 4 (event_id record) ++
      encode_uint_le 8 (trade_id record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (contracts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (event_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (contracts_value, bytes) =>
                              Some ({| time := time_value; instrument_id := instrument_id_value; event_id := event_id_value; trade_id := trade_id_value; price := price_value; contracts := contracts_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End LiquidityEventExecutionMessage.

  Module LiquidityEventCancelMessage.

    (** LiquidityEventCancelMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      event_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (event_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 4 (event_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (event_id_value, bytes) =>
                  Some ({| time := time_value; instrument_id := instrument_id_value; event_id := event_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End LiquidityEventCancelMessage.

  Module AddOrderNonCustomerMessage.

    (** AddOrderNonCustomerMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      order_id : N;
      side : N;
      price : N;
      contracts : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (contracts record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint 1 (side record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (contracts record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (contracts_value, bytes) =>
                              Some ({| time := time_value; instrument_id := instrument_id_value; order_id := order_id_value; side := side_value; price := price_value; contracts := contracts_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AddOrderNonCustomerMessage.

  Module AddOrderCustomerMessage.

    (** AddOrderCustomerMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      order_id : N;
      side : N;
      price : N;
      contracts : N;
      customer_indicator : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (customer_indicator record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint 1 (side record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (contracts record) ++
      encode_uint 1 (customer_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (contracts_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (customer_indicator_value, bytes) =>
                                  Some ({| time := time_value; instrument_id := instrument_id_value; order_id := order_id_value; side := side_value; price := price_value; contracts := contracts_value; customer_indicator := customer_indicator_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AddOrderCustomerMessage.

  Module ModifyOrderMessage.

    (** ModifyOrderMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      order_id : N;
      price : N;
      contracts : N;
      mod_flag : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      (mod_flag record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (contracts record) ++
      encode_uint 1 (mod_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (contracts_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (mod_flag_value, bytes) =>
                              Some ({| time := time_value; instrument_id := instrument_id_value; order_id := order_id_value; price := price_value; contracts := contracts_value; mod_flag := mod_flag_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ModifyOrderMessage.

  Module DeleteOrderMessage.

    (** DeleteOrderMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  Some ({| time := time_value; instrument_id := instrument_id_value; order_id := order_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End DeleteOrderMessage.

  Module OrderExecutionMessage.

    (** OrderExecutionMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      order_id : N;
      trade_id : N;
      price : N;
      executed_contracts : N;
      remaining_contracts : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (executed_contracts record < 256 ^ N.of_nat 4)%N /\
      (remaining_contracts record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (trade_id record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (executed_contracts record) ++
      encode_uint_le 4 (remaining_contracts record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (executed_contracts_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (remaining_contracts_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_condition_value, bytes) =>
                                      Some ({| time := time_value; instrument_id := instrument_id_value; order_id := order_id_value; trade_id := trade_id_value; price := price_value; executed_contracts := executed_contracts_value; remaining_contracts := remaining_contracts_value; trade_condition := trade_condition_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutionMessage.

  Module DeepTradeBreakMessage.

    (** DEEPTradeBreakMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  Some ({| time := time_value; instrument_id := instrument_id_value; trade_id := trade_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End DeepTradeBreakMessage.

  Module QuoteUpdateNoCustomerInterestMessage.

    (** QuoteUpdateNoCustomerInterestMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      bid_size : N;
      bid_price : N;
      ask_size : N;
      ask_price : N;
      status_status_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (ask_size record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 8)%N /\
      (status_status_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 4 (bid_size record) ++
      encode_uint_le 8 (bid_price record) ++
      encode_uint_le 4 (ask_size record) ++
      encode_uint_le 8 (ask_price record) ++
      encode_uint 1 (status_status_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (bid_size_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (bid_price_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (ask_size_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (ask_price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (status_status_type_value, bytes) =>
                                  Some ({| time := time_value; instrument_id := instrument_id_value; bid_size := bid_size_value; bid_price := bid_price_value; ask_size := ask_size_value; ask_price := ask_price_value; status_status_type := status_status_type_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End QuoteUpdateNoCustomerInterestMessage.

  Module QuoteUpdateCustomerInterestMessage.

    (** QuoteUpdateCustomerInterestMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      bid_size : N;
      bid_customer_size : N;
      bid_price : N;
      ask_size : N;
      ask_customer_size : N;
      ask_price : N;
      status_status_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (bid_customer_size record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (ask_size record < 256 ^ N.of_nat 4)%N /\
      (ask_customer_size record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 8)%N /\
      (status_status_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 4 (bid_size record) ++
      encode_uint_le 4 (bid_customer_size record) ++
      encode_uint_le 8 (bid_price record) ++
      encode_uint_le 4 (ask_size record) ++
      encode_uint_le 4 (ask_customer_size record) ++
      encode_uint_le 8 (ask_price record) ++
      encode_uint 1 (status_status_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (bid_size_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (bid_customer_size_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (bid_price_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (ask_size_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (ask_customer_size_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (ask_price_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (status_status_type_value, bytes) =>
                                          Some ({| time := time_value; instrument_id := instrument_id_value; bid_size := bid_size_value; bid_customer_size := bid_customer_size_value; bid_price := bid_price_value; ask_size := ask_size_value; ask_customer_size := ask_customer_size_value; ask_price := ask_price_value; status_status_type := status_status_type_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End QuoteUpdateCustomerInterestMessage.

  Module TradeMessage.

    (** TradeMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      trade_id : N;
      price : N;
      contracts : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (trade_id record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (contracts record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (contracts_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (trade_condition_value, bytes) =>
                              Some ({| time := time_value; instrument_id := instrument_id_value; trade_id := trade_id_value; price := price_value; contracts := contracts_value; trade_condition := trade_condition_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module TradeCorrectionMessage.

    (** TradeCorrectionMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      original_trade_id : N;
      trade_id : N;
      price : N;
      contracts : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (original_trade_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (contracts record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (original_trade_id record) ++
      encode_uint_le 8 (trade_id record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (contracts record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (original_trade_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (contracts_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_condition_value, bytes) =>
                                  Some ({| time := time_value; instrument_id := instrument_id_value; original_trade_id := original_trade_id_value; trade_id := trade_id_value; price := price_value; contracts := contracts_value; trade_condition := trade_condition_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

  Module TopsTradeBreakMessage.

    (** TOPSTradeBreakMessage *)
    Record t := {
      time : N;
      instrument_id : N;
      trade_id : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (time record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 8 (trade_id record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (trade_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trade_condition_value, bytes) =>
                      Some ({| time := time_value; instrument_id := instrument_id_value; trade_id := trade_id_value; trade_condition := trade_condition_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TopsTradeBreakMessage.

  Module HeartbeatMessage.

    (** HeartbeatMessage *)
    Record t := {
      channel_id : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (channel_id record) ++
      encode_uint_le 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              Some ({| channel_id := channel_id_value; sequence_number := sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End HeartbeatMessage.

  Module MessageListGroupEncoding.

    (** messageListGroupEncoding *)
    Record t := {
      block_length_short : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length_short record < 256 ^ N.of_nat 1)%N /\
      (num_in_group record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (block_length_short record) ++
      encode_uint 1 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (block_length_short_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length_short := block_length_short_value; num_in_group := num_in_group_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageListGroupEncoding.

  Module SessionShutdownMessage.

    (** SessionShutdownMessage *)
    Record t := {
      channel_id : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 4)%N /\
      (sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (channel_id record) ++
      encode_uint_le 8 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              Some ({| channel_id := channel_id_value; sequence_number := sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SessionShutdownMessage.

  Module RetransmissionRequestMessage.

    (** RetransmissionRequestMessage *)
    Record t := {
      begin_sequence : N;
      end_sequence : N;
      logon_id : list byte;
      request_id : N;
      channel_id : N;
      feed : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_sequence record < 256 ^ N.of_nat 8)%N /\
      (end_sequence record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (logon_id record) = 16 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (channel_id record < 256 ^ N.of_nat 4)%N /\
      (feed record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (begin_sequence record) ++
      encode_uint_le 8 (end_sequence record) ++
      encode_bytes 16 (logon_id record) ++
      encode_uint_le 4 (request_id record) ++
      encode_uint_le 4 (channel_id record) ++
      encode_uint 1 (feed record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (begin_sequence_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (end_sequence_value, bytes) =>
              match decode_bytes 16 bytes with
              | None => None
              | Some (logon_id_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (request_id_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (channel_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (feed_value, bytes) =>
                              Some ({| begin_sequence := begin_sequence_value; end_sequence := end_sequence_value; logon_id := logon_id_value; request_id := request_id_value; channel_id := channel_id_value; feed := feed_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmissionRequestMessage.

  Module RetransmissionResponseMessage.

    (** RetransmissionResponseMessage *)
    Record t := {
      logon_id : list byte;
      request_id : N;
      channel_id : N;
      feed : N;
      status_retransmission_status_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (logon_id record) = 16 /\
      (request_id record < 256 ^ N.of_nat 4)%N /\
      (channel_id record < 256 ^ N.of_nat 4)%N /\
      (feed record < 256 ^ N.of_nat 1)%N /\
      (status_retransmission_status_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (logon_id record) ++
      encode_uint_le 4 (request_id record) ++
      encode_uint_le 4 (channel_id record) ++
      encode_uint 1 (feed record) ++
      encode_uint 1 (status_retransmission_status_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (logon_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (request_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (channel_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (feed_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (status_retransmission_status_type_value, bytes) =>
                          Some ({| logon_id := logon_id_value; request_id := request_id_value; channel_id := channel_id_value; feed := feed_value; status_retransmission_status_type := status_retransmission_status_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmissionResponseMessage.

  Module SnapshotHeaderMessage.

    (** SnapshotHeaderMessage *)
    Record t := {
      snapshot_id : N;
      current_packet_number : N;
      total_packet_count : N;
      as_of_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (snapshot_id record < 256 ^ N.of_nat 4)%N /\
      (current_packet_number record < 256 ^ N.of_nat 4)%N /\
      (total_packet_count record < 256 ^ N.of_nat 4)%N /\
      (as_of_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (snapshot_id record) ++
      encode_uint_le 4 (current_packet_number record) ++
      encode_uint_le 4 (total_packet_count record) ++
      encode_uint_le 8 (as_of_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (snapshot_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (current_packet_number_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (total_packet_count_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (as_of_sequence_number_value, bytes) =>
                      Some ({| snapshot_id := snapshot_id_value; current_packet_number := current_packet_number_value; total_packet_count := total_packet_count_value; as_of_sequence_number := as_of_sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SnapshotHeaderMessage.

End IexOptionsMarketDataV103.
