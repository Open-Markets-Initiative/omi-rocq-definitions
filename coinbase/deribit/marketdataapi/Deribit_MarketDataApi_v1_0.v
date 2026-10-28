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
      - a Composite rule
      - a run counted by a field
  *)

Module DeribitMarketDataApiV10.

  Module GroupSizeEncoding.

    (** groupSizeEncoding *)
    Record t := {
      block_length : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 2 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding.

  Module GroupSizeEncoding2.

    (** groupSizeEncoding *)
    Record t := {
      block_length : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 2 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group := num_in_group_value |}, bytes)
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

  End GroupSizeEncoding2.

  Module IndexDefinitionMessage.

    (** IndexDefinitionMessage *)
    Record t := {
      index_id : N;
      name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (index_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (name record) = 128.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (index_id record) ++
      encode_bytes 128 (name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (index_id_value, bytes) =>
          match decode_bytes 128 bytes with
          | None => None
          | Some (name_value, bytes) =>
              Some ({| index_id := index_id_value; name := name_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 136.
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

  End IndexDefinitionMessage.

  Module InstrumentInfoMessage.

    (** InstrumentInfoMessage *)
    Record t := {
      instrument_id : N;
      min_sell_price : N;
      max_buy_price : N;
      index_price : N;
      mark_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (min_sell_price record < 256 ^ N.of_nat 8)%N /\
      (max_buy_price record < 256 ^ N.of_nat 8)%N /\
      (index_price record < 256 ^ N.of_nat 8)%N /\
      (mark_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (instrument_id record) ++
      encode_uint 8 (min_sell_price record) ++
      encode_uint 8 (max_buy_price record) ++
      encode_uint 8 (index_price record) ++
      encode_uint 8 (mark_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (min_sell_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (max_buy_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (index_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (mark_price_value, bytes) =>
                          Some ({| instrument_id := instrument_id_value; min_sell_price := min_sell_price_value; max_buy_price := max_buy_price_value; index_price := index_price_value; mark_price := mark_price_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End InstrumentInfoMessage.

  Module InstrumentRefMessage.

    (** InstrumentRefMessage *)
    Record t := {
      instrument_id : N;
      current_funding : N;
      funding_8h : N;
      estimated_delivery_price : N;
      delivery_price : N;
      settlement_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (current_funding record < 256 ^ N.of_nat 8)%N /\
      (funding_8h record < 256 ^ N.of_nat 8)%N /\
      (estimated_delivery_price record < 256 ^ N.of_nat 8)%N /\
      (delivery_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (instrument_id record) ++
      encode_uint 8 (current_funding record) ++
      encode_uint 8 (funding_8h record) ++
      encode_uint 8 (estimated_delivery_price record) ++
      encode_uint 8 (delivery_price record) ++
      encode_uint 8 (settlement_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (current_funding_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (funding_8h_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (estimated_delivery_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (delivery_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (settlement_price_value, bytes) =>
                              Some ({| instrument_id := instrument_id_value; current_funding := current_funding_value; funding_8h := funding_8h_value; estimated_delivery_price := estimated_delivery_price_value; delivery_price := delivery_price_value; settlement_price := settlement_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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

  End InstrumentRefMessage.

  Module InstrumentStatusUpdateMessage.

    (** InstrumentStatusUpdateMessage *)
    Record t := {
      instrument_id : N;
      trading_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (trading_status record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (instrument_id record) ++
      encode_uint 1 (trading_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (trading_status_value, bytes) =>
              Some ({| instrument_id := instrument_id_value; trading_status := trading_status_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End InstrumentStatusUpdateMessage.

  Module BidPutMessage.

    (** BidPutMessage *)
    Record t := {
      order_id : N;
      instrument_id : N;
      quantity_mantissa : N;
      price : N;
      sort_order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_mantissa record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (sort_order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_uint 8 (instrument_id record) ++
      encode_uint 8 (quantity_mantissa record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (sort_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_mantissa_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sort_order_id_value, bytes) =>
                          Some ({| order_id := order_id_value; instrument_id := instrument_id_value; quantity_mantissa := quantity_mantissa_value; price := price_value; sort_order_id := sort_order_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End BidPutMessage.

  Module AskPutMessage.

    (** AskPutMessage *)
    Record t := {
      order_id : N;
      instrument_id : N;
      quantity_mantissa : N;
      price : N;
      sort_order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_mantissa record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (sort_order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_uint 8 (instrument_id record) ++
      encode_uint 8 (quantity_mantissa record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (sort_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_mantissa_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sort_order_id_value, bytes) =>
                          Some ({| order_id := order_id_value; instrument_id := instrument_id_value; quantity_mantissa := quantity_mantissa_value; price := price_value; sort_order_id := sort_order_id_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End AskPutMessage.

  Module BidQtyReducedMessage.

    (** BidQtyReducedMessage *)
    Record t := {
      order_id : N;
      instrument_id : N;
      quantity_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_mantissa record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_uint 8 (instrument_id record) ++
      encode_uint 8 (quantity_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_mantissa_value, bytes) =>
                  Some ({| order_id := order_id_value; instrument_id := instrument_id_value; quantity_mantissa := quantity_mantissa_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End BidQtyReducedMessage.

  Module AskQtyReducedMessage.

    (** AskQtyReducedMessage *)
    Record t := {
      order_id : N;
      instrument_id : N;
      quantity_mantissa : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_mantissa record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_uint 8 (instrument_id record) ++
      encode_uint 8 (quantity_mantissa record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_mantissa_value, bytes) =>
                  Some ({| order_id := order_id_value; instrument_id := instrument_id_value; quantity_mantissa := quantity_mantissa_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End AskQtyReducedMessage.

  Module BidDeleteMessage.

    (** BidDeleteMessage *)
    Record t := {
      order_id : N;
      instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_uint 8 (instrument_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              Some ({| order_id := order_id_value; instrument_id := instrument_id_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BidDeleteMessage.

  Module AskDeleteMessage.

    (** AskDeleteMessage *)
    Record t := {
      order_id : N;
      instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (order_id record) ++
      encode_uint 8 (instrument_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              Some ({| order_id := order_id_value; instrument_id := instrument_id_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AskDeleteMessage.

  Module SnapshotHeaderMessage.

    (** SnapshotHeaderMessage *)
    Record t := {
      instrument_id : N;
      incremental_timestamp : N;
      incremental_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (incremental_timestamp record < 256 ^ N.of_nat 8)%N /\
      (incremental_seq_num record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (instrument_id record) ++
      encode_uint 8 (incremental_timestamp record) ++
      encode_uint 8 (incremental_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (incremental_timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (incremental_seq_num_value, bytes) =>
                  Some ({| instrument_id := instrument_id_value; incremental_timestamp := incremental_timestamp_value; incremental_seq_num := incremental_seq_num_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End SnapshotHeaderMessage.

  Module SnapshotTrailerMessage.

    (** SnapshotTrailerMessage *)
    Record t := {
      instrument_id : N;
      timestamp : N;
      increment_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (increment_seq_num record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (instrument_id record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (increment_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (increment_seq_num_value, bytes) =>
                  Some ({| instrument_id := instrument_id_value; timestamp := timestamp_value; increment_seq_num := increment_seq_num_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End SnapshotTrailerMessage.

  Module EndOfCycleMessage.

    (** EndOfCycleMessage *)
    Record t := {
      active_instrument_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (active_instrument_count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (active_instrument_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (active_instrument_count_value, bytes) =>
          Some ({| active_instrument_count := active_instrument_count_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EndOfCycleMessage.

  Module RetransmitRequestMessage.

    (** RetransmitRequestMessage *)
    Record t := {
      begin_seq_num : N;
      message_count_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (begin_seq_num record < 256 ^ N.of_nat 8)%N /\
      (message_count_short record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (begin_seq_num record) ++
      encode_uint 1 (message_count_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (begin_seq_num_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_short_value, bytes) =>
              Some ({| begin_seq_num := begin_seq_num_value; message_count_short := message_count_short_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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
      encode_uint 8 (retry_delay_nanos record) ++
      encode_bytes 40 (details record) ++
      encode_uint 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
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

  End RetransmitRejectMessage.

End DeribitMarketDataApiV10.
