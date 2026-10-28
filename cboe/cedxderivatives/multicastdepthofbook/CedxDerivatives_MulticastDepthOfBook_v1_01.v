From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Europe Derivatives Multicast Depth Of Book

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
      - a run counted by a field
      - a field read in bits
  *)

Module CedxDerivativesMulticastDepthOfBookV101.

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
      symbol_long : list byte;
      price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_long record) = 8 /\
      (price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 4 (quantity_long record) ++
      encode_bytes 8 (symbol_long record) ++
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
                      | Some (symbol_long_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity_long := quantity_long_value; symbol_long := symbol_long_value; price_long := price_long_value |}, bytes)
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
      symbol : list byte;
      price_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (quantity_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 6 /\
      (price_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 2 (quantity_short record) ++
      encode_bytes 6 (symbol record) ++
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
                      | Some (symbol_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (price_short_value, bytes) =>
                              Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; quantity_short := quantity_short_value; symbol := symbol_value; price_short := price_short_value |}, bytes)
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
      executed_quantity : N;
      execution_id : N;
      execution_flags : ExecutionFlags.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      ExecutionFlags.bounded (execution_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_quantity record) ++
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
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (execution_id_value, bytes) =>
                      match ExecutionFlags.decode bytes with
                      | None => None
                      | Some (execution_flags_value, bytes) =>
                          Some ({| time_offset := time_offset_value; order_id := order_id_value; executed_quantity := executed_quantity_value; execution_id := execution_id_value; execution_flags := execution_flags_value |}, bytes)
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
      executed_quantity : N;
      remaining_quantity : N;
      execution_id : N;
      price_long : N;
      execution_flags : ExecutionFlags2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (remaining_quantity record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      ExecutionFlags2.bounded (execution_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (remaining_quantity record) ++
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
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (remaining_quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (execution_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              match ExecutionFlags2.decode bytes with
                              | None => None
                              | Some (execution_flags_value, bytes) =>
                                  Some ({| time_offset := time_offset_value; order_id := order_id_value; executed_quantity := executed_quantity_value; remaining_quantity := remaining_quantity_value; execution_id := execution_id_value; price_long := price_long_value; execution_flags := execution_flags_value |}, bytes)
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
      cancelled_contracts_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (cancelled_contracts_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (cancelled_contracts_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (cancelled_contracts_long_value, bytes) =>
                  Some ({| time_offset := time_offset_value; order_id := order_id_value; cancelled_contracts_long := cancelled_contracts_long_value |}, bytes)
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
      cancelled_contracts_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (cancelled_contracts_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (cancelled_contracts_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (cancelled_contracts_short_value, bytes) =>
                  Some ({| time_offset := time_offset_value; order_id := order_id_value; cancelled_contracts_short := cancelled_contracts_short_value |}, bytes)
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
      contracts_long : N;
      price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (contracts_long record < 256 ^ N.of_nat 4)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (contracts_long record) ++
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
              | Some (contracts_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      Some ({| time_offset := time_offset_value; order_id := order_id_value; contracts_long := contracts_long_value; price_long := price_long_value |}, bytes)
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
      contracts_short : N;
      price_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (contracts_short record < 256 ^ N.of_nat 2)%N /\
      (price_short record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 2 (contracts_short record) ++
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
              | Some (contracts_short_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (price_short_value, bytes) =>
                      Some ({| time_offset := time_offset_value; order_id := order_id_value; contracts_short := contracts_short_value; price_short := price_short_value |}, bytes)
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
      contracts_long : N;
      symbol_long : list byte;
      price_long : N;
      execution_id : N;
      trade_flags : TradeFlags.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (contracts_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_long record) = 8 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      TradeFlags.bounded (trade_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 4 (contracts_long record) ++
      encode_bytes 8 (symbol_long record) ++
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
                  | Some (contracts_long_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (symbol_long_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (execution_id_value, bytes) =>
                                  match TradeFlags.decode bytes with
                                  | None => None
                                  | Some (trade_flags_value, bytes) =>
                                      Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; contracts_long := contracts_long_value; symbol_long := symbol_long_value; price_long := price_long_value; execution_id := execution_id_value; trade_flags := trade_flags_value |}, bytes)
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
      contracts_short : N;
      symbol : list byte;
      price_short : N;
      execution_id : N;
      trade_flags : TradeFlags2.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (side_indicator record) = 1 /\
      (contracts_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (symbol record) = 6 /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      TradeFlags2.bounded (trade_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 2 (contracts_short record) ++
      encode_bytes 6 (symbol record) ++
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
                  | Some (contracts_short_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (price_short_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (execution_id_value, bytes) =>
                                  match TradeFlags2.decode bytes with
                                  | None => None
                                  | Some (trade_flags_value, bytes) =>
                                      Some ({| time_offset := time_offset_value; order_id := order_id_value; side_indicator := side_indicator_value; contracts_short := contracts_short_value; symbol := symbol_value; price_short := price_short_value; execution_id := execution_id_value; trade_flags := trade_flags_value |}, bytes)
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
      contracts_extended : N;
      symbol_long : list byte;
      price_long : N;
      trade_id : N;
      trade_timestamp : N;
      execution_venue : list byte;
      currency : list byte;
      cboe_trade_flags : list byte;
      extended_trade_flags : ExtendedTradeFlags.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (contracts_extended record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 8 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (trade_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (execution_venue record) = 4 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (cboe_trade_flags record) = 1 /\
      ExtendedTradeFlags.bounded (extended_trade_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (contracts_extended record) ++
      encode_bytes 8 (symbol_long record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 8 (trade_timestamp record) ++
      encode_bytes 4 (execution_venue record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (cboe_trade_flags record) ++
      ExtendedTradeFlags.encode (extended_trade_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (contracts_extended_value, bytes) =>
              match decode_bytes 8 bytes with
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
                                      | Some (cboe_trade_flags_value, bytes) =>
                                          match ExtendedTradeFlags.decode bytes with
                                          | None => None
                                          | Some (extended_trade_flags_value, bytes) =>
                                              Some ({| time_offset := time_offset_value; contracts_extended := contracts_extended_value; symbol_long := symbol_long_value; price_long := price_long_value; trade_id := trade_id_value; trade_timestamp := trade_timestamp_value; execution_venue := execution_venue_value; currency := currency_value; cboe_trade_flags := cboe_trade_flags_value; extended_trade_flags := extended_trade_flags_value |}, bytes)
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
      symbol_long : list byte;
      status : list byte;
      reserved_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reserved_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (reserved_3_value, bytes) =>
                      Some ({| time_offset := time_offset_value; symbol_long := symbol_long_value; status := status_value; reserved_3 := reserved_3_value |}, bytes)
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

  Module AuctionSummaryMessage.

    (** Auction Summary Message *)
    Record t := {
      time_offset : N;
      symbol_long : list byte;
      auction_type : list byte;
      price_long : N;
      contracts_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (contracts_long record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 4 (contracts_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (contracts_long_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol_long := symbol_long_value; auction_type := auction_type_value; price_long := price_long_value; contracts_long := contracts_long_value |}, bytes)
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

  Module OpeningAuctionUpdateMessage.

    (** Opening Auction Update Message *)
    Record t := {
      time_offset : N;
      symbol_long : list byte;
      auction_type : list byte;
      reference_price : N;
      buy_contracts : N;
      sell_contracts : N;
      indicative_price : N;
      auction_only_price : N;
      opening_condition : list byte;
      composite_market_bid_price : N;
      composite_market_offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_long record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (buy_contracts record < 256 ^ N.of_nat 4)%N /\
      (sell_contracts record < 256 ^ N.of_nat 4)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (auction_only_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (opening_condition record) = 1 /\
      (composite_market_bid_price record < 256 ^ N.of_nat 8)%N /\
      (composite_market_offer_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol_long record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 4 (buy_contracts record) ++
      encode_uint 4 (sell_contracts record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 8 (auction_only_price record) ++
      encode_bytes 1 (opening_condition record) ++
      encode_uint 8 (composite_market_bid_price record) ++
      encode_uint 8 (composite_market_offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (reference_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (buy_contracts_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (sell_contracts_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (indicative_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (auction_only_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (opening_condition_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (composite_market_bid_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (composite_market_offer_price_value, bytes) =>
                                                  Some ({| time_offset := time_offset_value; symbol_long := symbol_long_value; auction_type := auction_type_value; reference_price := reference_price_value; buy_contracts := buy_contracts_value; sell_contracts := sell_contracts_value; indicative_price := indicative_price_value; auction_only_price := auction_only_price_value; opening_condition := opening_condition_value; composite_market_bid_price := composite_market_bid_price_value; composite_market_offer_price := composite_market_offer_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningAuctionUpdateMessage.

  Module AuctionNotificationMessage.

    (** Auction Notification Message *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      auction_id : N;
      auction_type : list byte;
      side : list byte;
      price_long : N;
      contracts_long : N;
      customer_indicator : list byte;
      participant_id : list byte;
      auction_end_offset : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (contracts_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (customer_indicator record) = 1 /\
      Datatypes.length (participant_id record) = 4 /\
      (auction_end_offset record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 8 (auction_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 4 (contracts_long record) ++
      encode_bytes 1 (customer_indicator record) ++
      encode_bytes 4 (participant_id record) ++
      encode_uint 4 (auction_end_offset record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (auction_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (auction_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (contracts_long_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (customer_indicator_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (participant_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (auction_end_offset_value, bytes) =>
                                              Some ({| time_offset := time_offset_value; symbol := symbol_value; auction_id := auction_id_value; auction_type := auction_type_value; side := side_value; price_long := price_long_value; contracts_long := contracts_long_value; customer_indicator := customer_indicator_value; participant_id := participant_id_value; auction_end_offset := auction_end_offset_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionNotificationMessage.

  Module AuctionCancelMessage.

    (** Auction Cancel Message *)
    Record t := {
      time_offset : N;
      auction_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (auction_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (auction_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (auction_id_value, bytes) =>
              Some ({| time_offset := time_offset_value; auction_id := auction_id_value |}, bytes)
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

  End AuctionCancelMessage.

  Module ExecutionFlags3.

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

  End ExecutionFlags3.

  Module AuctionTradeMessage.

    (** Auction Trade Message *)
    Record t := {
      time_offset : N;
      auction_id : N;
      execution_id : N;
      price_long : N;
      contracts_long : N;
      execution_flags : ExecutionFlags3.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (auction_id record < 256 ^ N.of_nat 8)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (contracts_long record < 256 ^ N.of_nat 4)%N /\
      ExecutionFlags3.bounded (execution_flags record).

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (auction_id record) ++
      encode_uint 8 (execution_id record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 4 (contracts_long record) ++
      ExecutionFlags3.encode (execution_flags record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (auction_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (execution_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_long_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (contracts_long_value, bytes) =>
                          match ExecutionFlags3.decode bytes with
                          | None => None
                          | Some (execution_flags_value, bytes) =>
                              Some ({| time_offset := time_offset_value; auction_id := auction_id_value; execution_id := execution_id_value; price_long := price_long_value; contracts_long := contracts_long_value; execution_flags := execution_flags_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !ExecutionFlags3.encode_length. reflexivity.
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
      rewrite ExecutionFlags3.decode_encode by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ExecutionFlags3.eq_dec]. Defined.

  End AuctionTradeMessage.

  Module WidthUpdateMessage.

    (** Width Update Message *)
    Record t := {
      time_offset : N;
      product_code : list byte;
      width_type : list byte;
      multiplier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (product_code record) = 8 /\
      Datatypes.length (width_type record) = 1 /\
      (multiplier record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (product_code record) ++
      encode_bytes 1 (width_type record) ++
      encode_uint 4 (multiplier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (product_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (width_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (multiplier_value, bytes) =>
                      Some ({| time_offset := time_offset_value; product_code := product_code_value; width_type := width_type_value; multiplier := multiplier_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End WidthUpdateMessage.

  Module FuturesInstrumentDefinitionMessage.

    (** Futures Instrument Definition Message *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      product_code : list byte;
      expiration_date : N;
      contract_size : N;
      listing_state : list byte;
      price_increment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (product_code record) = 8 /\
      (expiration_date record < 256 ^ N.of_nat 4)%N /\
      (contract_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (listing_state record) = 1 /\
      (price_increment record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 8 (product_code record) ++
      encode_uint 4 (expiration_date record) ++
      encode_uint 2 (contract_size record) ++
      encode_bytes 1 (listing_state record) ++
      encode_uint 8 (price_increment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (product_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (expiration_date_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (contract_size_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (listing_state_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_increment_value, bytes) =>
                                  Some ({| time_offset := time_offset_value; symbol := symbol_value; product_code := product_code_value; expiration_date := expiration_date_value; contract_size := contract_size_value; listing_state := listing_state_value; price_increment := price_increment_value |}, bytes)
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FuturesInstrumentDefinitionMessage.

  Module OptionsInstrumentDefinitionMessage.

    (** Options Instrument Definition Message *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      product_code : list byte;
      call_put : list byte;
      expiration_date : N;
      strike_price : N;
      contract_size : N;
      listing_state : list byte;
      price_increment : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (product_code record) = 8 /\
      Datatypes.length (call_put record) = 1 /\
      (expiration_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (contract_size record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (listing_state record) = 1 /\
      (price_increment record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 8 (product_code record) ++
      encode_bytes 1 (call_put record) ++
      encode_uint 4 (expiration_date record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 2 (contract_size record) ++
      encode_bytes 1 (listing_state record) ++
      encode_uint 8 (price_increment record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (product_code_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (call_put_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (contract_size_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (listing_state_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (price_increment_value, bytes) =>
                                          Some ({| time_offset := time_offset_value; symbol := symbol_value; product_code := product_code_value; call_put := call_put_value; expiration_date := expiration_date_value; strike_price := strike_price_value; contract_size := contract_size_value; listing_state := listing_state_value; price_increment := price_increment_value |}, bytes)
                                      end
                                  end
                              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsInstrumentDefinitionMessage.

  Module TradeBreakMessage.

    (** Trade Break Message *)
    Record t := {
      time_offset : N;
      execution_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (execution_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (execution_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (execution_id_value, bytes) =>
              Some ({| time_offset := time_offset_value; execution_id := execution_id_value |}, bytes)
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

  End TradeBreakMessage.

  Module SettlementMessage.

    (** Settlement Message *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      trade_date : N;
      settlement_price : N;
      issue : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 6 /\
      (trade_date record < 256 ^ N.of_nat 4)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (issue record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 4 (trade_date record) ++
      encode_uint 8 (settlement_price record) ++
      encode_bytes 1 (issue record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (trade_date_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (settlement_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (issue_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol := symbol_value; trade_date := trade_date_value; settlement_price := settlement_price_value; issue := issue_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementMessage.

End CedxDerivativesMulticastDepthOfBookV101.
