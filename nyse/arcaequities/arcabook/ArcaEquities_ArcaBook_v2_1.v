From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * New York Stock Exchange ArcaBook

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

Module ArcaEquitiesArcaBookV21.

  Module MessageHeader.

    (** ArcaBook message header *)
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

  Module AddOrderMessage.

    (** ArcaBook Add Order Message *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      order_idgtc_indicator : N;
      trade_session : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_idgtc_indicator record < 256 ^ N.of_nat 1)%N /\
      (trade_session record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (order_idgtc_indicator record) ++
      encode_uint 1 (trade_session record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (order_idgtc_indicator_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (trade_session_value, bytes) =>
                                          Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; order_idgtc_indicator := order_idgtc_indicator_value; trade_session := trade_session_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module ModifyOrderMessage.

    (** ArcaBook Modify Order Message *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      order_idgtc_indicator : N;
      reason_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_idgtc_indicator record < 256 ^ N.of_nat 1)%N /\
      (reason_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (order_idgtc_indicator record) ++
      encode_uint 1 (reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (order_idgtc_indicator_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (reason_code_value, bytes) =>
                                          Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; order_idgtc_indicator := order_idgtc_indicator_value; reason_code := reason_code_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ModifyOrderMessage.

  Module DeleteOrderMessage.

    (** ArcaBook Delete Order Message *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      side : list byte;
      order_idgtc_indicator : N;
      reason_code : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_idgtc_indicator record < 256 ^ N.of_nat 1)%N /\
      (reason_code record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (order_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (order_idgtc_indicator record) ++
      encode_uint 1 (reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (order_idgtc_indicator_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reason_code_value, bytes) =>
                                  Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; side := side_value; order_idgtc_indicator := order_idgtc_indicator_value; reason_code := reason_code_value |}, bytes)
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DeleteOrderMessage.

  Module ExecutionMessage.

    (** ArcaBook Execution Message *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      order_idgtc_indicator : N;
      reason_code : N;
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (order_idgtc_indicator record < 256 ^ N.of_nat 1)%N /\
      (reason_code record < 256 ^ N.of_nat 1)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_uint 1 (order_idgtc_indicator record) ++
      encode_uint 1 (reason_code record) ++
      encode_uint 4 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_idgtc_indicator_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (reason_code_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (trade_id_value, bytes) =>
                                          Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; order_idgtc_indicator := order_idgtc_indicator_value; reason_code := reason_code_value; trade_id := trade_id_value |}, bytes)
                                      end
                                  end
                              end
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

  End ExecutionMessage.

  Module ImbalanceMessage.

    (** ArcaBook Imbalance Message *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      indicative_match_price : N;
      paired_qty : N;
      total_imbalance_qty : N;
      market_imbalance_qty : N;
      auction_time : N;
      auction_type : list byte;
      imbalance_side : list byte;
      continuous_book_clearing_price : N;
      closing_only_clearing_price : N;
      ssr_filing_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (indicative_match_price record < 256 ^ N.of_nat 4)%N /\
      (paired_qty record < 256 ^ N.of_nat 4)%N /\
      (total_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (market_imbalance_qty record < 256 ^ N.of_nat 4)%N /\
      (auction_time record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (imbalance_side record) = 1 /\
      (continuous_book_clearing_price record < 256 ^ N.of_nat 4)%N /\
      (closing_only_clearing_price record < 256 ^ N.of_nat 4)%N /\
      (ssr_filing_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (indicative_match_price record) ++
      encode_uint 4 (paired_qty record) ++
      encode_uint 4 (total_imbalance_qty record) ++
      encode_uint 4 (market_imbalance_qty record) ++
      encode_uint 2 (auction_time record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (imbalance_side record) ++
      encode_uint 4 (continuous_book_clearing_price record) ++
      encode_uint 4 (closing_only_clearing_price record) ++
      encode_uint 4 (ssr_filing_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (indicative_match_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (paired_qty_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (total_imbalance_qty_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (market_imbalance_qty_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (auction_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (auction_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (imbalance_side_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (continuous_book_clearing_price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (closing_only_clearing_price_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (ssr_filing_price_value, bytes) =>
                                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; indicative_match_price := indicative_match_price_value; paired_qty := paired_qty_value; total_imbalance_qty := total_imbalance_qty_value; market_imbalance_qty := market_imbalance_qty_value; auction_time := auction_time_value; auction_type := auction_type_value; imbalance_side := imbalance_side_value; continuous_book_clearing_price := continuous_book_clearing_price_value; closing_only_clearing_price := closing_only_clearing_price_value; ssr_filing_price := ssr_filing_price_value |}, bytes)
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ImbalanceMessage.

  Module AddOrderRefreshMessage.

    (** ArcaBook Add Order Refresh Message *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      order_idgtc_indicator : N;
      trade_session : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_idgtc_indicator record < 256 ^ N.of_nat 1)%N /\
      (trade_session record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (order_idgtc_indicator record) ++
      encode_uint 1 (trade_session record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (order_idgtc_indicator_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trade_session_value, bytes) =>
                                              Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; order_idgtc_indicator := order_idgtc_indicator_value; trade_session := trade_session_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderRefreshMessage.

  Module AttributedAddOrderMessage.

    (** ArcaBook Attributed Add Order Message *)
    Record t := {
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      order_idgtc_indicator : N;
      trade_session : N;
      firm_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_idgtc_indicator record < 256 ^ N.of_nat 1)%N /\
      (trade_session record < 256 ^ N.of_nat 1)%N /\
      (firm_id record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (order_idgtc_indicator record) ++
      encode_uint 1 (trade_session record) ++
      encode_uint 5 (firm_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_ns_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (symbol_index_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (order_idgtc_indicator_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (trade_session_value, bytes) =>
                                          match decode_uint 5 bytes with
                                          | None => None
                                          | Some (firm_id_value, bytes) =>
                                              Some ({| source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; order_idgtc_indicator := order_idgtc_indicator_value; trade_session := trade_session_value; firm_id := firm_id_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AttributedAddOrderMessage.

  Module AttributedAddOrderRefreshMessage.

    (** ArcaBook Attributed Add Order Refresh Message *)
    Record t := {
      source_time : N;
      source_time_ns : N;
      symbol_index : N;
      symbol_seq_num : N;
      order_id : N;
      price : N;
      volume : N;
      side : list byte;
      order_idgtc_indicator : N;
      trade_session : N;
      firm_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (source_time record < 256 ^ N.of_nat 4)%N /\
      (source_time_ns record < 256 ^ N.of_nat 4)%N /\
      (symbol_index record < 256 ^ N.of_nat 4)%N /\
      (symbol_seq_num record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_idgtc_indicator record < 256 ^ N.of_nat 1)%N /\
      (trade_session record < 256 ^ N.of_nat 1)%N /\
      (firm_id record < 256 ^ N.of_nat 5)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (source_time record) ++
      encode_uint 4 (source_time_ns record) ++
      encode_uint 4 (symbol_index record) ++
      encode_uint 4 (symbol_seq_num record) ++
      encode_uint 4 (order_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 1 (side record) ++
      encode_uint 1 (order_idgtc_indicator record) ++
      encode_uint 1 (trade_session record) ++
      encode_uint 5 (firm_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (source_time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (source_time_ns_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (symbol_index_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (symbol_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (order_idgtc_indicator_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (trade_session_value, bytes) =>
                                              match decode_uint 5 bytes with
                                              | None => None
                                              | Some (firm_id_value, bytes) =>
                                                  Some ({| source_time := source_time_value; source_time_ns := source_time_ns_value; symbol_index := symbol_index_value; symbol_seq_num := symbol_seq_num_value; order_id := order_id_value; price := price_value; volume := volume_value; side := side_value; order_idgtc_indicator := order_idgtc_indicator_value; trade_session := trade_session_value; firm_id := firm_id_value |}, bytes)
                                              end
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
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AttributedAddOrderRefreshMessage.

End ArcaEquitiesArcaBookV21.
