From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Multicast Depth Of Book

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
      - a field read in bits
  *)

Module BxeEquitiesMulticastDepthOfBookV624.

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

  Module TimeMessage.

    (** Time *)
    Record t := {
      time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          Some ({| time := time_value |}, bytes)
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

  End TimeMessage.

  Module UnitClearMessage.

    (** Unit Clear *)
    Record t := {
      time_offset : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          Some ({| time_offset := time_offset_value |}, bytes)
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

  End UnitClearMessage.

  Module AddOrderLongMessage.

    (** Add Order — Long *)
    Record t := {
      time_offset : N;
      order_id : N;
      side_indicator : list byte;
      quantity_long : N;
      symbol_short : list byte;
      price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      (price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 4 (quantity_long record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_uint 8 (price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_long_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (symbol_short_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity_long := quantity_long_value; symbol_short := symbol_short_value; price_long := price_long_value |}, bytes)
                          end
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

  End AddOrderLongMessage.

  Module AddOrderShortMessage.

    (** Add Order — Short *)
    Record t := {
      time_offset : N;
      order_id : N;
      side_indicator : list byte;
      quantity_short : N;
      symbol_alphanumeric_6 : list byte;
      price_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol_alphanumeric_6 record) = 6 /\
      (price_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 2 (quantity_short record) ++
      encode_bytes 6 (symbol_alphanumeric_6 record) ++
      encode_uint 2 (price_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (quantity_short_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_alphanumeric_6_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (price_short_value, bytes) =>
                              Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity_short := quantity_short_value; symbol_alphanumeric_6 := symbol_alphanumeric_6_value; price_short := price_short_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End AddOrderShortMessage.

  Module ExecutionFlags.

    (** Execution Flags *)
    Record t := {
      market_mechanism : list byte;
      trading_mode : list byte;
      ex_cum_dividend : list byte;
      algorithmic_trade : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (ex_cum_dividend record) = 1 /\
      Datatypes.length (algorithmic_trade record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (ex_cum_dividend record) ++
      encode_bytes 1 (algorithmic_trade record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_mechanism_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_mode_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (ex_cum_dividend_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (algorithmic_trade_value, bytes) =>
                      Some ({| market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; ex_cum_dividend := ex_cum_dividend_value; algorithmic_trade := algorithmic_trade_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionFlags.

  Module OrderExecutedMessage.

    (** Order Executed *)
    Record t := {
      time_offset : N;
      order_id : N;
      executed_shares : N;
      execution_id : N;
      execution_flags : ExecutionFlags.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_shares record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      ExecutionFlags.bounded (execution_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_shares record) ++
      encode_uint 8 (execution_id record) ++
      ExecutionFlags.encode (execution_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_shares_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (execution_id_value, bytes) =>
                      match ExecutionFlags.decode bytes with
                      | None => None
                      | Some (execution_flags_value, bytes) =>
                          Some ({| time_offset := time_offset_value; order_id := order_id_value; executed_shares := executed_shares_value; execution_id := execution_id_value; execution_flags := execution_flags_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !ExecutionFlags.encode_length. reflexivity.
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
      rewrite ExecutionFlags.decode_encode by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ExecutionFlags.eq_dec]. Defined.

  End OrderExecutedMessage.

  Module ExecutionFlags2.

    (** Execution Flags *)
    Record t := {
      market_mechanism : list byte;
      trading_mode : list byte;
      ex_cum_dividend : list byte;
      algorithmic_trade : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (ex_cum_dividend record) = 1 /\
      Datatypes.length (algorithmic_trade record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (ex_cum_dividend record) ++
      encode_bytes 1 (algorithmic_trade record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_mechanism_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_mode_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (ex_cum_dividend_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (algorithmic_trade_value, bytes) =>
                      Some ({| market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; ex_cum_dividend := ex_cum_dividend_value; algorithmic_trade := algorithmic_trade_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExecutionFlags2.

  Module OrderExecutedAtPriceSizeMessage.

    (** Order Executed at Price/Size *)
    Record t := {
      time_offset : N;
      order_id : N;
      executed_shares : N;
      remaining_shares : N;
      execution_id : N;
      price_long : N;
      execution_flags : ExecutionFlags2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_shares record < 256 ^ N.of_nat 4)%N /\
      (remaining_shares record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      ExecutionFlags2.bounded (execution_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_shares record) ++
      encode_uint 4 (remaining_shares record) ++
      encode_uint 8 (execution_id record) ++
      encode_uint 8 (price_long record) ++
      ExecutionFlags2.encode (execution_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_shares_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (remaining_shares_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (execution_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              match ExecutionFlags2.decode bytes with
                              | None => None
                              | Some (execution_flags_value, bytes) =>
                                  Some ({| time_offset := time_offset_value; order_id := order_id_value; executed_shares := executed_shares_value; remaining_shares := remaining_shares_value; execution_id := execution_id_value; price_long := price_long_value; execution_flags := execution_flags_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !ExecutionFlags2.encode_length. reflexivity.
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
      rewrite ExecutionFlags2.decode_encode by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ExecutionFlags2.eq_dec]. Defined.

  End OrderExecutedAtPriceSizeMessage.

  Module ReduceSizeLongMessage.

    (** Reduce Size — Long *)
    Record t := {
      time_offset : N;
      order_id : N;
      cancelled_shares_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (cancelled_shares_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (cancelled_shares_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (cancelled_shares_long_value, bytes) =>
                  Some ({| time_offset := time_offset_value; order_id := order_id_value; cancelled_shares_long := cancelled_shares_long_value |}, bytes)
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

  End ReduceSizeLongMessage.

  Module ReduceSizeShortMessage.

    (** Reduce Size — Short *)
    Record t := {
      time_offset : N;
      order_id : N;
      cancelled_shares_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (cancelled_shares_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (cancelled_shares_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (cancelled_shares_short_value, bytes) =>
                  Some ({| time_offset := time_offset_value; order_id := order_id_value; cancelled_shares_short := cancelled_shares_short_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ReduceSizeShortMessage.

  Module ModifyOrderLongMessage.

    (** Modify Order — Long *)
    Record t := {
      time_offset : N;
      order_id : N;
      shares_long : N;
      price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (shares_long record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (shares_long record) ++
      encode_uint 8 (price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (shares_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      Some ({| time_offset := time_offset_value; order_id := order_id_value; shares_long := shares_long_value; price_long := price_long_value |}, bytes)
                  end
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

  End ModifyOrderLongMessage.

  Module ModifyOrderShortMessage.

    (** Modify Order — Short *)
    Record t := {
      time_offset : N;
      order_id : N;
      shares_short : N;
      price_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (shares_short record < 256 ^ N.of_nat 2)%N /\
      (price_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (shares_short record) ++
      encode_uint 2 (price_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (shares_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (price_short_value, bytes) =>
                      Some ({| time_offset := time_offset_value; order_id := order_id_value; shares_short := shares_short_value; price_short := price_short_value |}, bytes)
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

  End ModifyOrderShortMessage.

  Module DeleteOrderMessage.

    (** Delete Order *)
    Record t := {
      time_offset : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              Some ({| time_offset := time_offset_value; order_id := order_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End DeleteOrderMessage.

  Module TradeFlags.

    (** Trade Flags *)
    Record t := {
      market_mechanism : list byte;
      trading_mode : list byte;
      transaction_category : list byte;
      benchmark_reference_price_indicator : list byte;
      algorithmic_trade : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (transaction_category record) = 1 /\
      Datatypes.length (benchmark_reference_price_indicator record) = 1 /\
      Datatypes.length (algorithmic_trade record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_bytes 1 (benchmark_reference_price_indicator record) ++
      encode_bytes 1 (algorithmic_trade record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_mechanism_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_mode_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (transaction_category_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (benchmark_reference_price_indicator_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (algorithmic_trade_value, bytes) =>
                          Some ({| market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; transaction_category := transaction_category_value; benchmark_reference_price_indicator := benchmark_reference_price_indicator_value; algorithmic_trade := algorithmic_trade_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End TradeFlags.

  Module TradeLongMessage.

    (** Trade — Long *)
    Record t := {
      time_offset : N;
      order_id : N;
      side_indicator : list byte;
      shares_long : N;
      symbol_short : list byte;
      price_long : N;
      execution_id : N;
      trade_flags : TradeFlags.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (shares_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      TradeFlags.bounded (trade_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 4 (shares_long record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (execution_id record) ++
      TradeFlags.encode (trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (shares_long_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (symbol_short_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (execution_id_value, bytes) =>
                                  match TradeFlags.decode bytes with
                                  | None => None
                                  | Some (trade_flags_value, bytes) =>
                                      Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; shares_long := shares_long_value; symbol_short := symbol_short_value; price_long := price_long_value; execution_id := execution_id_value; trade_flags := trade_flags_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !TradeFlags.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite TradeFlags.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TradeFlags.eq_dec]. Defined.

  End TradeLongMessage.

  Module TradeFlags2.

    (** Trade Flags *)
    Record t := {
      market_mechanism : list byte;
      trading_mode : list byte;
      transaction_category : list byte;
      benchmark_reference_price_indicator : list byte;
      algorithmic_trade : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (transaction_category record) = 1 /\
      Datatypes.length (benchmark_reference_price_indicator record) = 1 /\
      Datatypes.length (algorithmic_trade record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_bytes 1 (benchmark_reference_price_indicator record) ++
      encode_bytes 1 (algorithmic_trade record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_mechanism_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_mode_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (transaction_category_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (benchmark_reference_price_indicator_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (algorithmic_trade_value, bytes) =>
                          Some ({| market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; transaction_category := transaction_category_value; benchmark_reference_price_indicator := benchmark_reference_price_indicator_value; algorithmic_trade := algorithmic_trade_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End TradeFlags2.

  Module TradeShortMessage.

    (** Trade — Short *)
    Record t := {
      time_offset : N;
      order_id : N;
      side_indicator : list byte;
      shares_short : N;
      symbol_alphanumeric_6 : list byte;
      price_short : N;
      execution_id : N;
      trade_flags : TradeFlags2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (shares_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol_alphanumeric_6 record) = 6 /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      TradeFlags2.bounded (trade_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 2 (shares_short record) ++
      encode_bytes 6 (symbol_alphanumeric_6 record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 8 (execution_id record) ++
      TradeFlags2.encode (trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (shares_short_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_alphanumeric_6_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (price_short_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (execution_id_value, bytes) =>
                                  match TradeFlags2.decode bytes with
                                  | None => None
                                  | Some (trade_flags_value, bytes) =>
                                      Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; shares_short := shares_short_value; symbol_alphanumeric_6 := symbol_alphanumeric_6_value; price_short := price_short_value; execution_id := execution_id_value; trade_flags := trade_flags_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !TradeFlags2.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite TradeFlags2.decode_encode by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply TradeFlags2.eq_dec]. Defined.

  End TradeShortMessage.

  Module ExtendedTradeFlags.

    (** Extended Trade Flags *)
    Record t := {
      market_mechanism : list byte;
      trading_mode : list byte;
      transaction_category : list byte;
      negotiated_trade : list byte;
      crossing_trade : list byte;
      modification_indicator : list byte;
      benchmark_reference_price_indicator : list byte;
      special_dividend : list byte;
      off_book_automated_indicator : list byte;
      price_formation_discovery_process : list byte;
      algorithmic_indicator : list byte;
      publication_mode_deferral_reason : list byte;
      deferral_or_enrichement_type : list byte;
      duplicative_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (transaction_category record) = 1 /\
      Datatypes.length (negotiated_trade record) = 1 /\
      Datatypes.length (crossing_trade record) = 1 /\
      Datatypes.length (modification_indicator record) = 1 /\
      Datatypes.length (benchmark_reference_price_indicator record) = 1 /\
      Datatypes.length (special_dividend record) = 1 /\
      Datatypes.length (off_book_automated_indicator record) = 1 /\
      Datatypes.length (price_formation_discovery_process record) = 1 /\
      Datatypes.length (algorithmic_indicator record) = 1 /\
      Datatypes.length (publication_mode_deferral_reason record) = 1 /\
      Datatypes.length (deferral_or_enrichement_type record) = 1 /\
      Datatypes.length (duplicative_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_bytes 1 (negotiated_trade record) ++
      encode_bytes 1 (crossing_trade record) ++
      encode_bytes 1 (modification_indicator record) ++
      encode_bytes 1 (benchmark_reference_price_indicator record) ++
      encode_bytes 1 (special_dividend record) ++
      encode_bytes 1 (off_book_automated_indicator record) ++
      encode_bytes 1 (price_formation_discovery_process record) ++
      encode_bytes 1 (algorithmic_indicator record) ++
      encode_bytes 1 (publication_mode_deferral_reason record) ++
      encode_bytes 1 (deferral_or_enrichement_type record) ++
      encode_bytes 1 (duplicative_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_mechanism_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_mode_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (transaction_category_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (negotiated_trade_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (crossing_trade_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (modification_indicator_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (benchmark_reference_price_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (special_dividend_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (off_book_automated_indicator_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (price_formation_discovery_process_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (algorithmic_indicator_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (publication_mode_deferral_reason_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (deferral_or_enrichement_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (duplicative_indicator_value, bytes) =>
                                                              Some ({| market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; transaction_category := transaction_category_value; negotiated_trade := negotiated_trade_value; crossing_trade := crossing_trade_value; modification_indicator := modification_indicator_value; benchmark_reference_price_indicator := benchmark_reference_price_indicator_value; special_dividend := special_dividend_value; off_book_automated_indicator := off_book_automated_indicator_value; price_formation_discovery_process := price_formation_discovery_process_value; algorithmic_indicator := algorithmic_indicator_value; publication_mode_deferral_reason := publication_mode_deferral_reason_value; deferral_or_enrichement_type := deferral_or_enrichement_type_value; duplicative_indicator := duplicative_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ExtendedTradeFlags.

  Module TradeExtendedMessage.

    (** Trade — Extended *)
    Record t := {
      time_offset : N;
      shares_extended : N;
      symbol_short : list byte;
      price_long : N;
      trade_id : N;
      trade_timestamp : N;
      execution_venue : list byte;
      currency : list byte;
      cboe_trade_timing_indicator : list byte;
      extended_trade_flags : ExtendedTradeFlags.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (shares_extended record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (trade_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (execution_venue record) = 4 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (cboe_trade_timing_indicator record) = 1 /\
      ExtendedTradeFlags.bounded (extended_trade_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (shares_extended record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (trade_timestamp record) ++
      encode_bytes 4 (execution_venue record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (cboe_trade_timing_indicator record) ++
      ExtendedTradeFlags.encode (extended_trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (shares_extended_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (symbol_short_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (trade_timestamp_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (execution_venue_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (currency_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (cboe_trade_timing_indicator_value, bytes) =>
                                          match ExtendedTradeFlags.decode bytes with
                                          | None => None
                                          | Some (extended_trade_flags_value, bytes) =>
                                              Some ({| time_offset := time_offset_value; shares_extended := shares_extended_value; symbol_short := symbol_short_value; price_long := price_long_value; trade_id := trade_id_value; trade_timestamp := trade_timestamp_value; execution_venue := execution_venue_value; currency := currency_value; cboe_trade_timing_indicator := cboe_trade_timing_indicator_value; extended_trade_flags := extended_trade_flags_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !ExtendedTradeFlags.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ExtendedTradeFlags.decode_encode by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExtendedTradeFlags.eq_dec]. Defined.

  End TradeExtendedMessage.

  Module ExtendedTradeFlags2.

    (** Extended Trade Flags *)
    Record t := {
      market_mechanism : list byte;
      trading_mode : list byte;
      transaction_category : list byte;
      negotiated_trade : list byte;
      crossing_trade : list byte;
      modification_indicator : list byte;
      benchmark_reference_price_indicator : list byte;
      special_dividend : list byte;
      off_book_automated_indicator : list byte;
      price_formation_discovery_process : list byte;
      algorithmic_indicator : list byte;
      publication_mode_deferral_reason : list byte;
      deferral_or_enrichement_type : list byte;
      duplicative_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (transaction_category record) = 1 /\
      Datatypes.length (negotiated_trade record) = 1 /\
      Datatypes.length (crossing_trade record) = 1 /\
      Datatypes.length (modification_indicator record) = 1 /\
      Datatypes.length (benchmark_reference_price_indicator record) = 1 /\
      Datatypes.length (special_dividend record) = 1 /\
      Datatypes.length (off_book_automated_indicator record) = 1 /\
      Datatypes.length (price_formation_discovery_process record) = 1 /\
      Datatypes.length (algorithmic_indicator record) = 1 /\
      Datatypes.length (publication_mode_deferral_reason record) = 1 /\
      Datatypes.length (deferral_or_enrichement_type record) = 1 /\
      Datatypes.length (duplicative_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_bytes 1 (negotiated_trade record) ++
      encode_bytes 1 (crossing_trade record) ++
      encode_bytes 1 (modification_indicator record) ++
      encode_bytes 1 (benchmark_reference_price_indicator record) ++
      encode_bytes 1 (special_dividend record) ++
      encode_bytes 1 (off_book_automated_indicator record) ++
      encode_bytes 1 (price_formation_discovery_process record) ++
      encode_bytes 1 (algorithmic_indicator record) ++
      encode_bytes 1 (publication_mode_deferral_reason record) ++
      encode_bytes 1 (deferral_or_enrichement_type record) ++
      encode_bytes 1 (duplicative_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_mechanism_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_mode_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (transaction_category_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (negotiated_trade_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (crossing_trade_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (modification_indicator_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (benchmark_reference_price_indicator_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (special_dividend_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (off_book_automated_indicator_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (price_formation_discovery_process_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (algorithmic_indicator_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (publication_mode_deferral_reason_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (deferral_or_enrichement_type_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (duplicative_indicator_value, bytes) =>
                                                              Some ({| market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; transaction_category := transaction_category_value; negotiated_trade := negotiated_trade_value; crossing_trade := crossing_trade_value; modification_indicator := modification_indicator_value; benchmark_reference_price_indicator := benchmark_reference_price_indicator_value; special_dividend := special_dividend_value; off_book_automated_indicator := off_book_automated_indicator_value; price_formation_discovery_process := price_formation_discovery_process_value; algorithmic_indicator := algorithmic_indicator_value; publication_mode_deferral_reason := publication_mode_deferral_reason_value; deferral_or_enrichement_type := deferral_or_enrichement_type_value; duplicative_indicator := duplicative_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ExtendedTradeFlags2.

  Module TradeUnknownSymbolMessage.

    (** Trade — Unknown Symbol *)
    Record t := {
      time_offset : N;
      shares_extended : N;
      symbol_long : list byte;
      price_long : N;
      trade_id : N;
      trade_timestamp : N;
      execution_venue : list byte;
      currency : list byte;
      cboe_trade_timing_indicator : list byte;
      extended_trade_flags : ExtendedTradeFlags2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (shares_extended record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 12 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (trade_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (execution_venue record) = 4 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (cboe_trade_timing_indicator record) = 1 /\
      ExtendedTradeFlags2.bounded (extended_trade_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (shares_extended record) ++
      encode_bytes 12 (symbol_long record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (trade_timestamp record) ++
      encode_bytes 4 (execution_venue record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (cboe_trade_timing_indicator record) ++
      ExtendedTradeFlags2.encode (extended_trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (shares_extended_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (symbol_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (trade_timestamp_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (execution_venue_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (currency_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (cboe_trade_timing_indicator_value, bytes) =>
                                          match ExtendedTradeFlags2.decode bytes with
                                          | None => None
                                          | Some (extended_trade_flags_value, bytes) =>
                                              Some ({| time_offset := time_offset_value; shares_extended := shares_extended_value; symbol_long := symbol_long_value; price_long := price_long_value; trade_id := trade_id_value; trade_timestamp := trade_timestamp_value; execution_venue := execution_venue_value; currency := currency_value; cboe_trade_timing_indicator := cboe_trade_timing_indicator_value; extended_trade_flags := extended_trade_flags_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 70.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length, !ExtendedTradeFlags2.encode_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite ExtendedTradeFlags2.decode_encode by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ExtendedTradeFlags2.eq_dec]. Defined.

  End TradeUnknownSymbolMessage.

  Module EndOfSessionMessage.

    (** End of Session *)
    Record t := {
      time_offset : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          Some ({| time_offset := time_offset_value |}, bytes)
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

  End EndOfSessionMessage.

  Module TransactionBeginMessage.

    (** Transaction Begin *)
    Record t := {
      time_offset : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          Some ({| time_offset := time_offset_value |}, bytes)
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

  End TransactionBeginMessage.

  Module TransactionEndMessage.

    (** Transaction End *)
    Record t := {
      time_offset : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          Some ({| time_offset := time_offset_value |}, bytes)
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

  End TransactionEndMessage.

  Module TradingStatusMessage.

    (** Trading Status *)
    Record t := {
      time_offset : N;
      symbol_short : list byte;
      status : list byte;
      reserved_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (reserved_3_value, bytes) =>
                      Some ({| time_offset := time_offset_value; symbol_short := symbol_short_value; status := status_value; reserved_3 := reserved_3_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module StatisticsMessage.

    (** Statistics Message *)
    Record t := {
      time_offset : N;
      symbol_short : list byte;
      price_long : N;
      statistic_type : list byte;
      price_determination : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (statistic_type record) = 1 /\
      Datatypes.length (price_determination record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_uint 8 (price_long record) ++
      encode_bytes 1 (statistic_type record) ++
      encode_bytes 1 (price_determination record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (statistic_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (price_determination_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol_short := symbol_short_value; price_long := price_long_value; statistic_type := statistic_type_value; price_determination := price_determination_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatisticsMessage.

  Module AuctionUpdateMessage.

    (** Auction Update Message *)
    Record t := {
      time_offset : N;
      symbol_short : list byte;
      auction_type : list byte;
      reference_price : N;
      indicative_price : N;
      indicative_shares : N;
      outside_tolerance : list byte;
      includes_primary : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (indicative_shares record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (outside_tolerance record) = 1 /\
      Datatypes.length (includes_primary record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 4 (indicative_shares record) ++
      encode_bytes 1 (outside_tolerance record) ++
      encode_bytes 1 (includes_primary record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (reference_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (indicative_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (indicative_shares_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (outside_tolerance_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (includes_primary_value, bytes) =>
                                      Some ({| time_offset := time_offset_value; symbol_short := symbol_short_value; auction_type := auction_type_value; reference_price := reference_price_value; indicative_price := indicative_price_value; indicative_shares := indicative_shares_value; outside_tolerance := outside_tolerance_value; includes_primary := includes_primary_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionUpdateMessage.

  Module AuctionSummaryMessage.

    (** Auction Summary Message *)
    Record t := {
      time_offset : N;
      symbol_short : list byte;
      auction_type : list byte;
      price_long : N;
      shares_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (shares_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 4 (shares_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (shares_long_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol_short := symbol_short_value; auction_type := auction_type_value; price_long := price_long_value; shares_long := shares_long_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionSummaryMessage.

End BxeEquitiesMulticastDepthOfBookV624.
