From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Coinbase Market Data Api

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
      - a field read in bits
      - a run counted by a field
      - a block whose stated length holds more than its fields

    License: MIT No Attribution
  *)

Module CoinbaseDerivativesMarketDataApiV12.

  Module MessageHeader.

    (** Coinbase Sbe Market Data message header — frame length plus standard SBE header *)
    Record t := {
      frame_length : N;
      block_length : N;
      template_id : N;
      schema_id : N;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (frame_length record < 256 ^ N.of_nat 2)%N /\
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (template_id record < 256 ^ N.of_nat 2)%N /\
      (schema_id record < 256 ^ N.of_nat 2)%N /\
      (version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (frame_length record) ++
      encode_uint_le 2 (block_length record) ++
      encode_uint_le 2 (template_id record) ++
      encode_uint_le 2 (schema_id record) ++
      encode_uint_le 2 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (frame_length_value, bytes) =>
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
                          Some ({| frame_length := frame_length_value; block_length := block_length_value; template_id := template_id_value; schema_id := schema_id_value; version := version_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
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
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module InstrHeader.

    (** Instrument Header *)
    Record t := {
      instrument_flags : N;
      instrument_side : N;
      instrument_id : N;
      instr_seq_num : N;
      trading_session_date : N;
      reserved : N;
      transact_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_flags record < 256 ^ N.of_nat 1)%N /\
      (instrument_side record < 256 ^ N.of_nat 1)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (reserved record < 256 ^ N.of_nat 2)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (instrument_flags record) ++
      encode_uint 1 (instrument_side record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint_le 4 (instr_seq_num record) ++
      encode_uint_le 2 (trading_session_date record) ++
      encode_uint_le 2 (reserved record) ++
      encode_uint_le 8 (transact_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (instrument_flags_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (instrument_side_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (instr_seq_num_value, bytes) =>
                      match decode_uint_le 2 bytes with
                      | None => None
                      | Some (trading_session_date_value, bytes) =>
                          match decode_uint_le 2 bytes with
                          | None => None
                          | Some (reserved_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (transact_time_value, bytes) =>
                                  Some ({| instrument_flags := instrument_flags_value; instrument_side := instrument_side_value; instrument_id := instrument_id_value; instr_seq_num := instr_seq_num_value; trading_session_date := trading_session_date_value; reserved := reserved_value; transact_time := transact_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_uint_le_length. reflexivity.
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
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrHeader.

  Module TradingStatusUpdateMessage.

    (** TradingStatusUpdateMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      limit_down_price : N;
      limit_up_price : N;
      trading_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (limit_down_price record < 256 ^ N.of_nat 8)%N /\
      (limit_up_price record < 256 ^ N.of_nat 8)%N /\
      (trading_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (limit_down_price record) ++
      encode_uint_le 8 (limit_up_price record) ++
      encode_uint 1 (trading_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (limit_down_price_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (limit_up_price_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      Some ({| instr_header := instr_header_value; limit_down_price := limit_down_price_value; limit_up_price := limit_up_price_value; trading_status := trading_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End TradingStatusUpdateMessage.

  Module OrderPutMessage.

    (** OrderPutMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      order_id : N;
      price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      Some ({| instr_header := instr_header_value; order_id := order_id_value; price := price_value; quantity := quantity_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End OrderPutMessage.

  Module OrderDeleteMessage.

    (** OrderDeleteMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              Some ({| instr_header := instr_header_value; order_id := order_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End OrderDeleteMessage.

  Module ImpliedOrderUpdateMessage.

    (** ImpliedOrderUpdateMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      best_price : N;
      next_price : N;
      best_qty : N;
      next_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (best_price record < 256 ^ N.of_nat 8)%N /\
      (next_price record < 256 ^ N.of_nat 8)%N /\
      (best_qty record < 256 ^ N.of_nat 4)%N /\
      (next_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (best_price record) ++
      encode_uint_le 8 (next_price record) ++
      encode_uint_le 4 (best_qty record) ++
      encode_uint_le 4 (next_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (best_price_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (next_price_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (best_qty_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (next_qty_value, bytes) =>
                          Some ({| instr_header := instr_header_value; best_price := best_price_value; next_price := next_price_value; best_qty := best_qty_value; next_qty := next_qty_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End ImpliedOrderUpdateMessage.

  Module TradeSummaryMessage.

    (** TradeSummaryMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      aggressor_order_id : N;
      aggressor_receive_time : N;
      vwap_price : N;
      deepest_price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (aggressor_order_id record < 256 ^ N.of_nat 8)%N /\
      (aggressor_receive_time record < 256 ^ N.of_nat 8)%N /\
      (vwap_price record < 256 ^ N.of_nat 8)%N /\
      (deepest_price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (aggressor_order_id record) ++
      encode_uint_le 8 (aggressor_receive_time record) ++
      encode_uint_le 8 (vwap_price record) ++
      encode_uint_le 8 (deepest_price record) ++
      encode_uint_le 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (aggressor_order_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (aggressor_receive_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (vwap_price_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (deepest_price_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              Some ({| instr_header := instr_header_value; aggressor_order_id := aggressor_order_id_value; aggressor_receive_time := aggressor_receive_time_value; vwap_price := vwap_price_value; deepest_price := deepest_price_value; quantity := quantity_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 58.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End TradeSummaryMessage.

  Module TradeMessage.

    (** TradeMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      match_id : N;
      buy_order_id : N;
      sell_order_id : N;
      price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (buy_order_id record < 256 ^ N.of_nat 8)%N /\
      (sell_order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (match_id record) ++
      encode_uint_le 8 (buy_order_id record) ++
      encode_uint_le 8 (sell_order_id record) ++
      encode_uint_le 8 (price record) ++
      encode_uint_le 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (match_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (buy_order_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (sell_order_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              Some ({| instr_header := instr_header_value; match_id := match_id_value; buy_order_id := buy_order_id_value; sell_order_id := sell_order_id_value; price := price_value; quantity := quantity_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 58.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End TradeMessage.

  Module TradeAmendMessage.

    (** TradeAmendMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      match_id : N;
      buy_order_id : N;
      sell_order_id : N;
      old_price : N;
      new_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (buy_order_id record < 256 ^ N.of_nat 8)%N /\
      (sell_order_id record < 256 ^ N.of_nat 8)%N /\
      (old_price record < 256 ^ N.of_nat 8)%N /\
      (new_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (match_id record) ++
      encode_uint_le 8 (buy_order_id record) ++
      encode_uint_le 8 (sell_order_id record) ++
      encode_uint_le 8 (old_price record) ++
      encode_uint_le 8 (new_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (match_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (buy_order_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (sell_order_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (old_price_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (new_price_value, bytes) =>
                              Some ({| instr_header := instr_header_value; match_id := match_id_value; buy_order_id := buy_order_id_value; sell_order_id := sell_order_id_value; old_price := old_price_value; new_price := new_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End TradeAmendMessage.

  Module SpreadTradeAmendMessage.

    (** SpreadTradeAmendMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      match_id : N;
      buy_order_id : N;
      sell_order_id : N;
      old_price : N;
      new_price : N;
      old_leg_1_price : N;
      new_leg_1_price : N;
      old_leg_2_price : N;
      new_leg_2_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (buy_order_id record < 256 ^ N.of_nat 8)%N /\
      (sell_order_id record < 256 ^ N.of_nat 8)%N /\
      (old_price record < 256 ^ N.of_nat 8)%N /\
      (new_price record < 256 ^ N.of_nat 8)%N /\
      (old_leg_1_price record < 256 ^ N.of_nat 8)%N /\
      (new_leg_1_price record < 256 ^ N.of_nat 8)%N /\
      (old_leg_2_price record < 256 ^ N.of_nat 8)%N /\
      (new_leg_2_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (match_id record) ++
      encode_uint_le 8 (buy_order_id record) ++
      encode_uint_le 8 (sell_order_id record) ++
      encode_uint_le 8 (old_price record) ++
      encode_uint_le 8 (new_price record) ++
      encode_uint_le 8 (old_leg_1_price record) ++
      encode_uint_le 8 (new_leg_1_price record) ++
      encode_uint_le 8 (old_leg_2_price record) ++
      encode_uint_le 8 (new_leg_2_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (match_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (buy_order_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (sell_order_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (old_price_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (new_price_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (old_leg_1_price_value, bytes) =>
                                  match decode_uint_le 8 bytes with
                                  | None => None
                                  | Some (new_leg_1_price_value, bytes) =>
                                      match decode_uint_le 8 bytes with
                                      | None => None
                                      | Some (old_leg_2_price_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (new_leg_2_price_value, bytes) =>
                                              Some ({| instr_header := instr_header_value; match_id := match_id_value; buy_order_id := buy_order_id_value; sell_order_id := sell_order_id_value; old_price := old_price_value; new_price := new_price_value; old_leg_1_price := old_leg_1_price_value; new_leg_1_price := new_leg_1_price_value; old_leg_2_price := old_leg_2_price_value; new_leg_2_price := new_leg_2_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End SpreadTradeAmendMessage.

  Module TradeBustMessage.

    (** TradeBustMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      match_id : N;
      buy_order_id : N;
      sell_order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (buy_order_id record < 256 ^ N.of_nat 8)%N /\
      (sell_order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (match_id record) ++
      encode_uint_le 8 (buy_order_id record) ++
      encode_uint_le 8 (sell_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (match_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (buy_order_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (sell_order_id_value, bytes) =>
                      Some ({| instr_header := instr_header_value; match_id := match_id_value; buy_order_id := buy_order_id_value; sell_order_id := sell_order_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End TradeBustMessage.

  Module MarketStatMessage.

    (** MarketStatMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      price : N;
      stat_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (stat_type record) = 1.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (price record) ++
      encode_bytes 1 (stat_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (stat_type_value, bytes) =>
                  Some ({| instr_header := instr_header_value; price := price_value; stat_type := stat_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InstrHeader.eq_dec]. Defined.

  End MarketStatMessage.

  Module TradeSessionVolumeMessage.

    (** TradeSessionVolumeMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      vwap_price : N;
      trade_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (vwap_price record < 256 ^ N.of_nat 8)%N /\
      (trade_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 8 (vwap_price record) ++
      encode_uint_le 4 (trade_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (vwap_price_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (trade_volume_value, bytes) =>
                  Some ({| instr_header := instr_header_value; vwap_price := vwap_price_value; trade_volume := trade_volume_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End TradeSessionVolumeMessage.

  Module OpenInterestMessage.

    (** OpenInterestMessage *)
    Record t := {
      instr_header : InstrHeader.t;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      InstrHeader.bounded (instr_header record) /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      InstrHeader.encode (instr_header record) ++
      encode_uint_le 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match InstrHeader.decode bytes with
      | None => None
      | Some (instr_header_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              Some ({| instr_header := instr_header_value; quantity := quantity_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !InstrHeader.encode_length, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite InstrHeader.decode_encode by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply InstrHeader.eq_dec]. Defined.

  End OpenInterestMessage.

  Module StartOfOutrightInstrumentSnapshotMessage.

    (** StartOfOutrightInstrumentSnapshotMessage *)
    Record t := {
      snapshot_seq_num : N;
      last_instr_seq_num : N;
      symbol : list byte;
      product_code : list byte;
      description : list byte;
      price_increment : N;
      cfi_code : list byte;
      currency : list byte;
      product_id : N;
      contract_size : N;
      order_count : N;
      first_trading_session_date : N;
      last_trading_session_date : N;
      trading_session_date : N;
      product_group : N;
      trading_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (snapshot_seq_num record < 256 ^ N.of_nat 2)%N /\
      (last_instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 24 /\
      Datatypes.length (product_code record) = 8 /\
      Datatypes.length (description record) = 32 /\
      (price_increment record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cfi_code record) = 8 /\
      Datatypes.length (currency record) = 8 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (contract_size record < 256 ^ N.of_nat 4)%N /\
      (order_count record < 256 ^ N.of_nat 4)%N /\
      (first_trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (last_trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (product_group record < 256 ^ N.of_nat 1)%N /\
      (trading_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (snapshot_seq_num record) ++
      encode_uint_le 4 (last_instr_seq_num record) ++
      encode_bytes 24 (symbol record) ++
      encode_bytes 8 (product_code record) ++
      encode_bytes 32 (description record) ++
      encode_uint_le 8 (price_increment record) ++
      encode_bytes 8 (cfi_code record) ++
      encode_bytes 8 (currency record) ++
      encode_uint_le 4 (product_id record) ++
      encode_uint_le 4 (contract_size record) ++
      encode_uint_le 4 (order_count record) ++
      encode_uint_le 2 (first_trading_session_date record) ++
      encode_uint_le 2 (last_trading_session_date record) ++
      encode_uint_le 2 (trading_session_date record) ++
      encode_uint 1 (product_group record) ++
      encode_uint 1 (trading_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (snapshot_seq_num_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (last_instr_seq_num_value, bytes) =>
              match decode_bytes 24 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (product_code_value, bytes) =>
                      match decode_bytes 32 bytes with
                      | None => None
                      | Some (description_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (price_increment_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (cfi_code_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (currency_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (product_id_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (contract_size_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (order_count_value, bytes) =>
                                                  match decode_uint_le 2 bytes with
                                                  | None => None
                                                  | Some (first_trading_session_date_value, bytes) =>
                                                      match decode_uint_le 2 bytes with
                                                      | None => None
                                                      | Some (last_trading_session_date_value, bytes) =>
                                                          match decode_uint_le 2 bytes with
                                                          | None => None
                                                          | Some (trading_session_date_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (product_group_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (trading_status_value, bytes) =>
                                                                      Some ({| snapshot_seq_num := snapshot_seq_num_value; last_instr_seq_num := last_instr_seq_num_value; symbol := symbol_value; product_code := product_code_value; description := description_value; price_increment := price_increment_value; cfi_code := cfi_code_value; currency := currency_value; product_id := product_id_value; contract_size := contract_size_value; order_count := order_count_value; first_trading_session_date := first_trading_session_date_value; last_trading_session_date := last_trading_session_date_value; trading_session_date := trading_session_date_value; product_group := product_group_value; trading_status := trading_status_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 114.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StartOfOutrightInstrumentSnapshotMessage.

  Module StartOfSpreadInstrumentSnapshotMessage.

    (** StartOfSpreadInstrumentSnapshotMessage *)
    Record t := {
      snapshot_seq_num : N;
      last_instr_seq_num : N;
      symbol : list byte;
      product_code : list byte;
      description : list byte;
      price_increment : N;
      cfi_code : list byte;
      currency : list byte;
      product_id : N;
      contract_size : N;
      order_count : N;
      first_trading_session_date : N;
      last_trading_session_date : N;
      trading_session_date : N;
      product_group : N;
      trading_status : N;
      leg_1_instrument_id : N;
      leg_2_instrument_id : N;
      spread_buy_convention : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (snapshot_seq_num record < 256 ^ N.of_nat 2)%N /\
      (last_instr_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 24 /\
      Datatypes.length (product_code record) = 8 /\
      Datatypes.length (description record) = 32 /\
      (price_increment record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cfi_code record) = 8 /\
      Datatypes.length (currency record) = 8 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (contract_size record < 256 ^ N.of_nat 4)%N /\
      (order_count record < 256 ^ N.of_nat 4)%N /\
      (first_trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (last_trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (trading_session_date record < 256 ^ N.of_nat 2)%N /\
      (product_group record < 256 ^ N.of_nat 1)%N /\
      (trading_status record < 256 ^ N.of_nat 1)%N /\
      (leg_1_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (leg_2_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (spread_buy_convention record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (snapshot_seq_num record) ++
      encode_uint_le 4 (last_instr_seq_num record) ++
      encode_bytes 24 (symbol record) ++
      encode_bytes 8 (product_code record) ++
      encode_bytes 32 (description record) ++
      encode_uint_le 8 (price_increment record) ++
      encode_bytes 8 (cfi_code record) ++
      encode_bytes 8 (currency record) ++
      encode_uint_le 4 (product_id record) ++
      encode_uint_le 4 (contract_size record) ++
      encode_uint_le 4 (order_count record) ++
      encode_uint_le 2 (first_trading_session_date record) ++
      encode_uint_le 2 (last_trading_session_date record) ++
      encode_uint_le 2 (trading_session_date record) ++
      encode_uint 1 (product_group record) ++
      encode_uint 1 (trading_status record) ++
      encode_uint_le 4 (leg_1_instrument_id record) ++
      encode_uint_le 4 (leg_2_instrument_id record) ++
      encode_uint 1 (spread_buy_convention record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (snapshot_seq_num_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (last_instr_seq_num_value, bytes) =>
              match decode_bytes 24 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (product_code_value, bytes) =>
                      match decode_bytes 32 bytes with
                      | None => None
                      | Some (description_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (price_increment_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (cfi_code_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (currency_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (product_id_value, bytes) =>
                                          match decode_uint_le 4 bytes with
                                          | None => None
                                          | Some (contract_size_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (order_count_value, bytes) =>
                                                  match decode_uint_le 2 bytes with
                                                  | None => None
                                                  | Some (first_trading_session_date_value, bytes) =>
                                                      match decode_uint_le 2 bytes with
                                                      | None => None
                                                      | Some (last_trading_session_date_value, bytes) =>
                                                          match decode_uint_le 2 bytes with
                                                          | None => None
                                                          | Some (trading_session_date_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (product_group_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (trading_status_value, bytes) =>
                                                                      match decode_uint_le 4 bytes with
                                                                      | None => None
                                                                      | Some (leg_1_instrument_id_value, bytes) =>
                                                                          match decode_uint_le 4 bytes with
                                                                          | None => None
                                                                          | Some (leg_2_instrument_id_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (spread_buy_convention_value, bytes) =>
                                                                                  Some ({| snapshot_seq_num := snapshot_seq_num_value; last_instr_seq_num := last_instr_seq_num_value; symbol := symbol_value; product_code := product_code_value; description := description_value; price_increment := price_increment_value; cfi_code := cfi_code_value; currency := currency_value; product_id := product_id_value; contract_size := contract_size_value; order_count := order_count_value; first_trading_session_date := first_trading_session_date_value; last_trading_session_date := last_trading_session_date_value; trading_session_date := trading_session_date_value; product_group := product_group_value; trading_status := trading_status_value; leg_1_instrument_id := leg_1_instrument_id_value; leg_2_instrument_id := leg_2_instrument_id_value; spread_buy_convention := spread_buy_convention_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 123.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint_le by exact bound_16.
      rewrite decode_encode_uint_le by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StartOfSpreadInstrumentSnapshotMessage.

  Module OrderSnapshotMessage.

    (** OrderSnapshotMessage *)
    Record t := {
      snapshot_seq_num : N;
      quantity : N;
      transact_time : N;
      order_id : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (snapshot_seq_num record < 256 ^ N.of_nat 2)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (snapshot_seq_num record) ++
      encode_uint_le 4 (quantity record) ++
      encode_uint_le 8 (transact_time record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (snapshot_seq_num_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (quantity_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (transact_time_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| snapshot_seq_num := snapshot_seq_num_value; quantity := quantity_value; transact_time := transact_time_value; order_id := order_id_value; price := price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
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
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderSnapshotMessage.

  Module RetransmitRequestMessage.

    (** RetransmitRequestMessage *)
    Record t := {
      begin_seq_num : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_num record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (begin_seq_num record) ++
      encode_uint 1 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (begin_seq_num_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              Some ({| begin_seq_num := begin_seq_num_value; message_count := message_count_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End RetransmitRequestMessage.

  Module RetransmitRejectMessage.

    (** RetransmitRejectMessage *)
    Record t := {
      retry_delay_nanos : N;
      details : list byte;
      reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (retry_delay_nanos record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (details record) = 40 /\
      (reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (retry_delay_nanos record) ++
      encode_bytes 40 (details record) ++
      encode_uint 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (retry_delay_nanos_value, bytes) =>
          match decode_bytes 40 bytes with
          | None => None
          | Some (details_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reason_value, bytes) =>
                  Some ({| retry_delay_nanos := retry_delay_nanos_value; details := details_value; reason := reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmitRejectMessage.

End CoinbaseDerivativesMarketDataApiV12.
