From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange Top Feed

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
      - a Composite rule
      - a run filling what frames it
  *)

Module ArcaOptionsTopFeedV13A.

  Module MessageHeader.

    Record t := {
      message_size : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      encode_uint 2 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_size := message_size_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  Module OutrightQuoteMessage.

    (** The Outright Quote message provides the price and aggregated volume for the best bid and best offer. Volumes aggregate quote and order interest. The message also indicates aggregated Customer volumes within the overall volumes. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      ask_price : N;
      bid_price : N;
      ask_volume : N;
      bid_volume : N;
      ask_customer_volume : N;
      bid_customer_volume : N;
      quote_condition : list byte;
      reserved_1 : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (ask_volume record < 256 ^ N.of_nat 2)%N /\
      (bid_volume record < 256 ^ N.of_nat 2)%N /\
      (ask_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (bid_customer_volume record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 2 (ask_volume record) ++
      encode_uint 2 (bid_volume record) ++
      encode_uint 2 (ask_customer_volume record) ++
      encode_uint 2 (bid_customer_volume record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_volume_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (bid_volume_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ask_customer_volume_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (bid_customer_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (reserved_2_value, bytes) =>
                                                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; ask_price := ask_price_value; bid_price := bid_price_value; ask_volume := ask_volume_value; bid_volume := bid_volume_value; ask_customer_volume := ask_customer_volume_value; bid_customer_volume := bid_customer_volume_value; quote_condition := quote_condition_value; reserved_1 := reserved_1_value; reserved_2 := reserved_2_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightQuoteMessage.

  Module OutrightTradeMessage.

    (** The Outright Trade message is used to publish all Last Sales for outright symbols. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      volume_4 : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume_4 record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_4_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_cond_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_2_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (reserved_2_value, bytes) =>
                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; volume_4 := volume_4_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightTradeMessage.

  Module OutrightTradeCancelMessage.

    (** The Trade Cancel message is used to cancel or bust a trade. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      original_trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (original_trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (original_trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_trade_id_value, bytes) =>
                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; original_trade_id := original_trade_id_value |}, bytes)
                      end
                  end
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

  End OutrightTradeCancelMessage.

  Module OutrightTradeCorrectionMessage.

    (** The Trade Correction message is used to correct a trade. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      original_trade_id : N;
      trade_id : N;
      price : N;
      volume_4 : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (original_trade_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (original_trade_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume_4 record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (original_trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_4_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_1_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_cond_2_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (reserved_2_value, bytes) =>
                                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; original_trade_id := original_trade_id_value; trade_id := trade_id_value; price := price_value; volume_4 := volume_4_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; reserved_2 := reserved_2_value |}, bytes)
                                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightTradeCorrectionMessage.

  Module OutrightImbalanceMessage.

    (** The Outright Imbalance message is sent during the Pre-opening phase or a symbol Halt to provide indicative opening price and net imbalance of all orders at that price which are orders eligible for next Auction. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      reference_price : N;
      paired_qty : N;
      total_imbalance_qty : N;
      market_imbalance_qty : N;
      auction_type : list byte;
      imbalance_side : list byte;
      market_imbalance_side : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (reference_price record < 256 ^ N.of_nat 4)%N /\
      (paired_qty record < 256 ^ N.of_nat 2)%N /\
      (total_imbalance_qty record < 256 ^ N.of_nat 2)%N /\
      (market_imbalance_qty record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (imbalance_side record) = 1 /\
      Datatypes.length (market_imbalance_side record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (reference_price record) ++
      encode_uint 2 (paired_qty record) ++
      encode_uint 2 (total_imbalance_qty record) ++
      encode_uint 2 (market_imbalance_qty record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (imbalance_side record) ++
      encode_bytes 1 (market_imbalance_side record) ++
      encode_uint 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (reference_price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (paired_qty_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (total_imbalance_qty_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (market_imbalance_qty_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (auction_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (imbalance_side_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (market_imbalance_side_value, bytes) =>
                                                  match decode_uint 3 bytes with
                                                  | None => None
                                                  | Some (reserved_3_value, bytes) =>
                                                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; reference_price := reference_price_value; paired_qty := paired_qty_value; total_imbalance_qty := total_imbalance_qty_value; market_imbalance_qty := market_imbalance_qty_value; auction_type := auction_type_value; imbalance_side := imbalance_side_value; market_imbalance_side := market_imbalance_side_value; reserved_3 := reserved_3_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightImbalanceMessage.

  Module OutrightCrossingRfqMessage.

    (** The Outright Crossing RFQ (Request for Quote) message is sent out in the event of an auction on an outright order. *)
    Record t := {
      source_time : N;
      source_ns : N;
      series_index : N;
      symbol_seq_num : N;
      side : list byte;
      reserved_1 : N;
      volume_2 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (volume_2 record < 256 ^ N.of_nat 2)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (volume_2 record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (volume_2_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| source_time := source_time_value; source_ns := source_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; side := side_value; reserved_1 := reserved_1_value; volume_2 := volume_2_value; price := price_value |}, bytes)
                                  end
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
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightCrossingRfqMessage.

  Module OutrightBoldRfqMessage.

    (** The Outright BOLD RFQ (Request for Quote) message notifies clients of a special exposure order (a BOLD order) available for execution on a first-come first-served basis. *)
    Record t := {
      source_time : N;
      source_ns : N;
      series_index : N;
      symbol_seq_num : N;
      side : list byte;
      capacity : list byte;
      contracts : N;
      price : N;
      participant : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (capacity record) = 1 /\
      (contracts record < 256 ^ N.of_nat 2)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (participant record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 1 (capacity record) ++
      encode_uint 2 (contracts record) ++
      encode_uint 4 (price record) ++
      encode_bytes 4 (participant record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (capacity_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (contracts_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (participant_value, bytes) =>
                                          Some ({| source_time := source_time_value; source_ns := source_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; side := side_value; capacity := capacity_value; contracts := contracts_value; price := price_value; participant := participant_value |}, bytes)
                                      end
                                  end
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightBoldRfqMessage.

  Module OutrightSummaryMessage.

    (** The Outright summary message provides trading highlights of the day. It is sent out once at the end of the trading day as soon as a symbol closes. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      high_price : N;
      low_price : N;
      open : N;
      close : N;
      total_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (high_price record < 256 ^ N.of_nat 4)%N /\
      (low_price record < 256 ^ N.of_nat 4)%N /\
      (open record < 256 ^ N.of_nat 4)%N /\
      (close record < 256 ^ N.of_nat 4)%N /\
      (total_volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (high_price record) ++
      encode_uint 4 (low_price record) ++
      encode_uint 4 (open record) ++
      encode_uint 4 (close record) ++
      encode_uint 4 (total_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (high_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (low_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (open_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (close_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (total_volume_value, bytes) =>
                                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; high_price := high_price_value; low_price := low_price_value; open := open_value; close := close_value; total_volume := total_volume_value |}, bytes)
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

  End OutrightSummaryMessage.

  Module UnderlyingStatusMessage.

    (** The Underlying Status message is used to inform the subscribers of changes in the status of an Underlying symbol. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      underlying_index : N;
      underlying_seq_num : N;
      security_status : list byte;
      halt_condition : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (underlying_index record < 256 ^ N.of_nat 4)%N /\
      (underlying_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_status record) = 1 /\
      Datatypes.length (halt_condition record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (underlying_index record) ++
      encode_uint 4 (underlying_seq_num record) ++
      encode_bytes 1 (security_status record) ++
      encode_bytes 1 (halt_condition record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (underlying_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (underlying_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (security_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (halt_condition_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (reserved_2_value, bytes) =>
                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; underlying_index := underlying_index_value; underlying_seq_num := underlying_seq_num_value; security_status := security_status_value; halt_condition := halt_condition_value; reserved_2 := reserved_2_value |}, bytes)
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingStatusMessage.

  Module OutrightSeriesStatusMessage.

    (** The Series Status message is used to inform the subscribers of changes in symbol status of an outright symbol. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      security_status : list byte;
      halt_condition : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (security_status record) = 1 /\
      Datatypes.length (halt_condition record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_bytes 1 (security_status record) ++
      encode_bytes 1 (halt_condition record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (security_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (halt_condition_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (reserved_2_value, bytes) =>
                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; security_status := security_status_value; halt_condition := halt_condition_value; reserved_2 := reserved_2_value |}, bytes)
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightSeriesStatusMessage.

  Module RefreshOutrightQuoteMessage.

    (** The Refresh Quote message is sent in the event no quote messages are published for the symbol for 2 consecutive minutes. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      ask_price : N;
      bid_price : N;
      ask_volume : N;
      bid_volume : N;
      ask_customer_volume : N;
      bid_customer_volume : N;
      quote_condition : list byte;
      reserved_1 : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (ask_volume record < 256 ^ N.of_nat 2)%N /\
      (bid_volume record < 256 ^ N.of_nat 2)%N /\
      (ask_customer_volume record < 256 ^ N.of_nat 2)%N /\
      (bid_customer_volume record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 2 (ask_volume record) ++
      encode_uint 2 (bid_volume record) ++
      encode_uint 2 (ask_customer_volume record) ++
      encode_uint 2 (bid_customer_volume record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (ask_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (ask_volume_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (bid_volume_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (ask_customer_volume_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (bid_customer_volume_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (quote_condition_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_uint 2 bytes with
                                                      | None => None
                                                      | Some (reserved_2_value, bytes) =>
                                                          Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; ask_price := ask_price_value; bid_price := bid_price_value; ask_volume := ask_volume_value; bid_volume := bid_volume_value; ask_customer_volume := ask_customer_volume_value; bid_customer_volume := bid_customer_volume_value; quote_condition := quote_condition_value; reserved_1 := reserved_1_value; reserved_2 := reserved_2_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshOutrightQuoteMessage.

  Module RefreshOutrightTradeMessage.

    (** The Refresh Outright Trade message is sent in the event no Outright Trade messages are published for the symbol for 2 consecutive minutes. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      trade_id : N;
      price : N;
      volume_4 : N;
      trade_cond_1 : list byte;
      trade_cond_2 : list byte;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_cond_1 record) = 1 /\
      Datatypes.length (trade_cond_2 record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume_4 record) ++
      encode_bytes 1 (trade_cond_1 record) ++
      encode_bytes 1 (trade_cond_2 record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_4_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_cond_1_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_cond_2_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (reserved_2_value, bytes) =>
                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; trade_id := trade_id_value; price := price_value; volume_4 := volume_4_value; trade_cond_1 := trade_cond_1_value; trade_cond_2 := trade_cond_2_value; reserved_2 := reserved_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshOutrightTradeMessage.

  Module RefreshOutrightImbalanceMessage.

    (** The Refresh Outright Imbalance message is sent in the event no Outright Imbalance messages are published for the symbol for 2 consecutive minutes during Pre-opening or a symbol Halt. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      series_index : N;
      symbol_seq_num : N;
      reference_price : N;
      paired_qty : N;
      total_imbalance_qty : N;
      market_imbalance_qty : N;
      auction_type : list byte;
      imbalance_side : list byte;
      market_imbalance_side : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (reference_price record < 256 ^ N.of_nat 4)%N /\
      (paired_qty record < 256 ^ N.of_nat 2)%N /\
      (total_imbalance_qty record < 256 ^ N.of_nat 2)%N /\
      (market_imbalance_qty record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (imbalance_side record) = 1 /\
      Datatypes.length (market_imbalance_side record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (series_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (reference_price record) ++
      encode_uint 2 (paired_qty record) ++
      encode_uint 2 (total_imbalance_qty record) ++
      encode_uint 2 (market_imbalance_qty record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (imbalance_side record) ++
      encode_bytes 1 (market_imbalance_side record) ++
      encode_uint 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (series_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (reference_price_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (paired_qty_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (total_imbalance_qty_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (market_imbalance_qty_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (auction_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (imbalance_side_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (market_imbalance_side_value, bytes) =>
                                                  match decode_uint 3 bytes with
                                                  | None => None
                                                  | Some (reserved_3_value, bytes) =>
                                                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; series_index := series_index_value; symbol_seq_num := symbol_seq_num_value; reference_price := reference_price_value; paired_qty := paired_qty_value; total_imbalance_qty := total_imbalance_qty_value; market_imbalance_qty := market_imbalance_qty_value; auction_type := auction_type_value; imbalance_side := imbalance_side_value; market_imbalance_side := market_imbalance_side_value; reserved_3 := reserved_3_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RefreshOutrightImbalanceMessage.

  Module UnderlyingIndexMappingMessage.

    (** On system startup, each multicast channel sends all the symbols on its channel. Underlying Index Mapping messages are published first, followed by all Series Index Mapping messages, and for the Complex feed, Complex Symbol Definitions last of all. *)
    Record t := {
      underlying_index : N;
      underlying_symbol : list byte;
      channel_id : N;
      market_id : N;
      system_id : N;
      exchange_code : list byte;
      price_scale_code : N;
      security_type : list byte;
      price_resolution : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (underlying_index record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      (channel_id record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 2)%N /\
      (system_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (exchange_code record) = 1 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (security_type record) = 1 /\
      (price_resolution record < 256 ^ N.of_nat 1)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (underlying_index record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_uint 1 (channel_id record) ++
      encode_uint 2 (market_id record) ++
      encode_uint 1 (system_id record) ++
      encode_bytes 1 (exchange_code record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 1 (security_type record) ++
      encode_uint 1 (price_resolution record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (underlying_index_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (underlying_symbol_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (channel_id_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (system_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (exchange_code_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (price_scale_code_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (security_type_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (price_resolution_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (reserved_1_value, bytes) =>
                                              Some ({| underlying_index := underlying_index_value; underlying_symbol := underlying_symbol_value; channel_id := channel_id_value; market_id := market_id_value; system_id := system_id_value; exchange_code := exchange_code_value; price_scale_code := price_scale_code_value; security_type := security_type_value; price_resolution := price_resolution_value; reserved_1 := reserved_1_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingIndexMappingMessage.

  Module SeriesIndexMappingMessage.

    (** On system startup, each multicast channel sends all the symbols on its channel. Underlying Index Mapping messages are published first, followed by all Series Index Mapping messages, and for the Complex feed, Complex Symbol Definitions last of all. *)
    Record t := {
      series_index : N;
      channel_id : N;
      reserved_a_1 : N;
      market_id : N;
      system_id : N;
      reserved_b_1 : N;
      stream_id : N;
      underlying_index : N;
      contract_multiplier : N;
      maturity_date : list byte;
      put_or_call : N;
      strike_price : list byte;
      price_scale_code : N;
      underlying_symbol : list byte;
      option_symbol_root : list byte;
      group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (series_index record < 256 ^ N.of_nat 4)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N /\
      (reserved_a_1 record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 2)%N /\
      (system_id record < 256 ^ N.of_nat 1)%N /\
      (reserved_b_1 record < 256 ^ N.of_nat 1)%N /\
      (stream_id record < 256 ^ N.of_nat 2)%N /\
      (underlying_index record < 256 ^ N.of_nat 4)%N /\
      (contract_multiplier record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (maturity_date record) = 6 /\
      (put_or_call record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (strike_price record) = 10 /\
      (price_scale_code record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (option_symbol_root record) = 5 /\
      (group_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (series_index record) ++
      encode_uint 1 (channel_id record) ++
      encode_uint 1 (reserved_a_1 record) ++
      encode_uint 2 (market_id record) ++
      encode_uint 1 (system_id record) ++
      encode_uint 1 (reserved_b_1 record) ++
      encode_uint 2 (stream_id record) ++
      encode_uint 4 (underlying_index record) ++
      encode_uint 2 (contract_multiplier record) ++
      encode_bytes 6 (maturity_date record) ++
      encode_uint 1 (put_or_call record) ++
      encode_bytes 10 (strike_price record) ++
      encode_uint 1 (price_scale_code record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 5 (option_symbol_root record) ++
      encode_uint 4 (group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (series_index_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (channel_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reserved_a_1_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (market_id_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (system_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_b_1_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (stream_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (underlying_index_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (contract_multiplier_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (maturity_date_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (put_or_call_value, bytes) =>
                                                  match decode_bytes 10 bytes with
                                                  | None => None
                                                  | Some (strike_price_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (price_scale_code_value, bytes) =>
                                                          match decode_bytes 11 bytes with
                                                          | None => None
                                                          | Some (underlying_symbol_value, bytes) =>
                                                              match decode_bytes 5 bytes with
                                                              | None => None
                                                              | Some (option_symbol_root_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (group_id_value, bytes) =>
                                                                      Some ({| series_index := series_index_value; channel_id := channel_id_value; reserved_a_1 := reserved_a_1_value; market_id := market_id_value; system_id := system_id_value; reserved_b_1 := reserved_b_1_value; stream_id := stream_id_value; underlying_index := underlying_index_value; contract_multiplier := contract_multiplier_value; maturity_date := maturity_date_value; put_or_call := put_or_call_value; strike_price := strike_price_value; price_scale_code := price_scale_code_value; underlying_symbol := underlying_symbol_value; option_symbol_root := option_symbol_root_value; group_id := group_id_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesIndexMappingMessage.

  Module StreamIdMessage.

    (** In all multicast channels, a Stream ID Message is sent immediately after each packet header to uniquely identify the source or Stream ID of the data in the packet. *)
    Record t := {
      stream_id : N;
      reserved_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stream_id record < 256 ^ N.of_nat 2)%N /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (stream_id record) ++
      encode_uint 2 (reserved_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (stream_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (reserved_2_value, bytes) =>
              Some ({| stream_id := stream_id_value; reserved_2 := reserved_2_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End StreamIdMessage.

  Module SequenceNumberResetMessage.

    (** This message is sent to reset the Message Sequence Number at start of day, or in response to failures. *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      product_id : N;
      channel_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 1)%N /\
      (channel_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 1 (product_id record) ++
      encode_uint 1 (channel_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (channel_id_value, bytes) =>
                      Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; product_id := product_id_value; channel_id := channel_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End SequenceNumberResetMessage.

End ArcaOptionsTopFeedV13A.
