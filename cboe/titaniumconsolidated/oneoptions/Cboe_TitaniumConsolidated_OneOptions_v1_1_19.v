From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange One Options

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
  *)

Module CboeTitaniumConsolidatedOneOptionsV1119.

  Module PacketHeader.

    Record t := {
      length_ : N;
      message_count : N;
      unit_ : N;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (unit_ record < 256 ^ N.of_nat 1)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 1 (unit_ record) ++
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (unit__value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; unit_ := unit__value; sequence := sequence_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 1)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module ShortSymbolSummaryMessage.

    (** The Short Symbol Summary message delivers the Cboe consolidated best bid/offer and total executed volume across all applicable Cboe One Options books. *)
    Record t := {
      last_update_timestamp : N;
      symbol : list byte;
      cboe_cumulative_executed_volume_short : N;
      consolidated_best_bid_price_short : N;
      consolidated_best_bid_quantity_short : N;
      consolidated_best_ask_price_short : N;
      consolidated_best_ask_quantity_short : N;
      reserved_5 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (cboe_cumulative_executed_volume_short record < 256 ^ N.of_nat 4)%N /\
      (consolidated_best_bid_price_short record < 256 ^ N.of_nat 4)%N /\
      (consolidated_best_bid_quantity_short record < 256 ^ N.of_nat 4)%N /\
      (consolidated_best_ask_price_short record < 256 ^ N.of_nat 4)%N /\
      (consolidated_best_ask_quantity_short record < 256 ^ N.of_nat 4)%N /\
      (reserved_5 record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 4 (cboe_cumulative_executed_volume_short record) ++
      encode_uint 4 (consolidated_best_bid_price_short record) ++
      encode_uint 4 (consolidated_best_bid_quantity_short record) ++
      encode_uint 4 (consolidated_best_ask_price_short record) ++
      encode_uint 4 (consolidated_best_ask_quantity_short record) ++
      encode_uint 5 (reserved_5 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (cboe_cumulative_executed_volume_short_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (consolidated_best_bid_price_short_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (consolidated_best_bid_quantity_short_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (consolidated_best_ask_price_short_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (consolidated_best_ask_quantity_short_value, bytes) =>
                                  match decode_uint 5 bytes with
                                  | None => None
                                  | Some (reserved_5_value, bytes) =>
                                      Some ({| last_update_timestamp := last_update_timestamp_value; symbol := symbol_value; cboe_cumulative_executed_volume_short := cboe_cumulative_executed_volume_short_value; consolidated_best_bid_price_short := consolidated_best_bid_price_short_value; consolidated_best_bid_quantity_short := consolidated_best_bid_quantity_short_value; consolidated_best_ask_price_short := consolidated_best_ask_price_short_value; consolidated_best_ask_quantity_short := consolidated_best_ask_quantity_short_value; reserved_5 := reserved_5_value |}, bytes)
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

  End ShortSymbolSummaryMessage.

  Module LongSymbolSummaryMessage.

    (** The Long Symbol Summary message delivers the Cboe consolidated best bid/offer and total executed volume across all applicable Cboe One Options books. *)
    Record t := {
      last_update_timestamp : N;
      symbol : list byte;
      cboe_cumulative_executed_volume_long : N;
      consolidated_best_bid_price_long : N;
      consolidated_best_bid_quantity_long : N;
      consolidated_best_ask_price_long : N;
      consolidated_best_ask_quantity_long : N;
      reserved_9 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      (cboe_cumulative_executed_volume_long record < 256 ^ N.of_nat 8)%N /\
      (consolidated_best_bid_price_long record < 256 ^ N.of_nat 8)%N /\
      (consolidated_best_bid_quantity_long record < 256 ^ N.of_nat 8)%N /\
      (consolidated_best_ask_price_long record < 256 ^ N.of_nat 8)%N /\
      (consolidated_best_ask_quantity_long record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_9 record) = 9.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_uint 8 (cboe_cumulative_executed_volume_long record) ++
      encode_uint 8 (consolidated_best_bid_price_long record) ++
      encode_uint 8 (consolidated_best_bid_quantity_long record) ++
      encode_uint 8 (consolidated_best_ask_price_long record) ++
      encode_uint 8 (consolidated_best_ask_quantity_long record) ++
      encode_bytes 9 (reserved_9 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cboe_cumulative_executed_volume_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consolidated_best_bid_price_long_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (consolidated_best_bid_quantity_long_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (consolidated_best_ask_price_long_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (consolidated_best_ask_quantity_long_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (reserved_9_value, bytes) =>
                                      Some ({| last_update_timestamp := last_update_timestamp_value; symbol := symbol_value; cboe_cumulative_executed_volume_long := cboe_cumulative_executed_volume_long_value; consolidated_best_bid_price_long := consolidated_best_bid_price_long_value; consolidated_best_bid_quantity_long := consolidated_best_bid_quantity_long_value; consolidated_best_ask_price_long := consolidated_best_ask_price_long_value; consolidated_best_ask_quantity_long := consolidated_best_ask_quantity_long_value; reserved_9 := reserved_9_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
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
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongSymbolSummaryMessage.

  Module BestQuoteUpdateMessage.

    (** The Best Quote Update message is used to update one side of the Cboe consolidated quote information for a symbol. Since the message only updates one side of the quote, the previous value for the other side of the quote remains in effect. This message does not affect the executed volume of the symbol. *)
    Record t := {
      last_update_timestamp : N;
      symbol : list byte;
      side_indicator : list byte;
      consolidated_best_quote_price : N;
      consolidated_quote_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (side_indicator record) = 1 /\
      (consolidated_best_quote_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_quote_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 8 (consolidated_best_quote_price record) ++
      encode_uint 8 (consolidated_quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consolidated_best_quote_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (consolidated_quote_quantity_value, bytes) =>
                          Some ({| last_update_timestamp := last_update_timestamp_value; symbol := symbol_value; side_indicator := side_indicator_value; consolidated_best_quote_price := consolidated_best_quote_price_value; consolidated_quote_quantity := consolidated_quote_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestQuoteUpdateMessage.

  Module CboeMarketStatusMessage.

    (** The Cboe Market Status message is disseminated to reflect a change in the status of a market. All markets should be assumed to be Normal unless otherwise indicated by a Cboe Market Status message. *)
    Record t := {
      timestamp : N;
      market_center : list byte;
      market_status : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (market_status record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (market_status record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_status_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (reserved_1_value, bytes) =>
                      Some ({| timestamp := timestamp_value; market_center := market_center_value; market_status := market_status_value; reserved_1 := reserved_1_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CboeMarketStatusMessage.

  Module TradeMessage.

    (** Trade messages are sent when an order is executed in whole or in part on a Cboe exchange. *)
    Record t := {
      transaction_time : N;
      symbol : list byte;
      market_center : list byte;
      market_center_execution_id : N;
      last_price : N;
      last_quantity : N;
      cboe_cumulative_executed_volume_long : N;
      trade_condition : list byte;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (market_center record) = 1 /\
      (market_center_execution_id record < 256 ^ N.of_nat 8)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (last_quantity record < 256 ^ N.of_nat 8)%N /\
      (cboe_cumulative_executed_volume_long record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_condition record) = 1 /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (market_center record) ++
      encode_uint 8 (market_center_execution_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (last_quantity record) ++
      encode_uint 8 (cboe_cumulative_executed_volume_long record) ++
      encode_bytes 1 (trade_condition record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (market_center_execution_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (last_quantity_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (cboe_cumulative_executed_volume_long_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_condition_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (reserved_8_value, bytes) =>
                                          Some ({| transaction_time := transaction_time_value; symbol := symbol_value; market_center := market_center_value; market_center_execution_id := market_center_execution_id_value; last_price := last_price_value; last_quantity := last_quantity_value; cboe_cumulative_executed_volume_long := cboe_cumulative_executed_volume_long_value; trade_condition := trade_condition_value; reserved_8 := reserved_8_value |}, bytes)
                                      end
                                  end
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module TradeBreakMessage.

    (** The Trade Break message is sent whenever an execution on a Cboe exchange is broken. Trade breaks are rare and only affect applications that rely upon Cboe execution based data. *)
    Record t := {
      transaction_time : N;
      symbol : list byte;
      market_center : list byte;
      market_center_execution_id : N;
      cboe_cumulative_executed_volume_long : N;
      reserved_9 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (market_center record) = 1 /\
      (market_center_execution_id record < 256 ^ N.of_nat 8)%N /\
      (cboe_cumulative_executed_volume_long record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reserved_9 record) = 9.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (market_center record) ++
      encode_uint 8 (market_center_execution_id record) ++
      encode_uint 8 (cboe_cumulative_executed_volume_long record) ++
      encode_bytes 9 (reserved_9 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (market_center_execution_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (cboe_cumulative_executed_volume_long_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (reserved_9_value, bytes) =>
                              Some ({| transaction_time := transaction_time_value; symbol := symbol_value; market_center := market_center_value; market_center_execution_id := market_center_execution_id_value; cboe_cumulative_executed_volume_long := cboe_cumulative_executed_volume_long_value; reserved_9 := reserved_9_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeBreakMessage.

  Module TradingStatusMessage.

    (** The Trading Status message is used to indicate the current trading status of an options contract on a Cboe exchange. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      market_center : list byte;
      halt_status : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (halt_status record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (halt_status record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (halt_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol := symbol_value; market_center := market_center_value; halt_status := halt_status_value; reserved_1 := reserved_1_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

End CboeTitaniumConsolidatedOneOptionsV1119.
