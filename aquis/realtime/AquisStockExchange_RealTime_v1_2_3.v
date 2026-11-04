From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Aquis Exchange Real Time Market Data Feed

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

    License: MIT No Attribution
  *)

Module AquisStockExchangeRealTimeV123.

  Module PacketHeader.

    (** Aquis udp packet header *)
    Record t := {
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_count record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_count_value, bytes) =>
          Some ({| message_count := message_count_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End PacketHeader.

  Module MessageHeader.

    (** Aquis market data message header *)
    Record t := {
      msg_type : N;
      msg_length : N;
      seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_type record < 256 ^ N.of_nat 1)%N /\
      (msg_length record < 256 ^ N.of_nat 1)%N /\
      (seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (msg_type record) ++
      encode_uint 1 (msg_length record) ++
      encode_uint 4 (seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (msg_type_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_length_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (seq_no_value, bytes) =>
                  Some ({| msg_type := msg_type_value; msg_length := msg_length_value; seq_no := seq_no_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End MessageHeader.

  Module OrderAddMessage.

    (** The Order Add message is published when order quantity is posted to the order book for a particular security. This message is only applicable to continuous trading. *)
    Record t := {
      security_id : N;
      side : N;
      quantity : N;
      price : N;
      order_ref : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_ref record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_ref_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (timestamp_value, bytes) =>
                              Some ({| security_id := security_id_value; side := side_value; quantity := quantity_value; price := price_value; order_ref := order_ref_value; timestamp := timestamp_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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

  End OrderAddMessage.

  Module OrderCancelMessage.

    (** The Order Cancel message is published when a visible order is removed from the book. This message is only applicable to continuous trading. *)
    Record t := {
      security_id : N;
      order_ref : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 4 (order_ref record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_ref_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  Some ({| security_id := security_id_value; order_ref := order_ref_value; timestamp := timestamp_value |}, bytes)
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

  End OrderCancelMessage.

  Module OrderModifyMessage.

    (** The Order Modify message is published when a visible order is modified by the client (change of price and/or quantity). The order reference number remains the same on order modification. This message is only applicable to continuous trading. *)
    Record t := {
      security_id : N;
      remaining_quantity : N;
      price : N;
      order_ref : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (remaining_quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_ref record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 4 (remaining_quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_ref record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (remaining_quantity_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_ref_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_value, bytes) =>
                          Some ({| security_id := security_id_value; remaining_quantity := remaining_quantity_value; price := price_value; order_ref := order_ref_value; timestamp := timestamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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

  End OrderModifyMessage.

  Module QuoteAddReplaceMessage.

    (** The Quote Add/Replace message is published when a quote is available for a particular security. *)
    Record t := {
      trader_id : N;
      security_id : N;
      bid_quantity : N;
      bid_price : N;
      offer_quantity : N;
      offer_price : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trader_id record < 256 ^ N.of_nat 2)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (bid_quantity record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (offer_quantity record < 256 ^ N.of_nat 4)%N /\
      (offer_price record < 256 ^ N.of_nat 8)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (trader_id record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 4 (bid_quantity record) ++
      encode_uint 8 (bid_price record) ++
      encode_uint 4 (offer_quantity record) ++
      encode_uint 8 (offer_price record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bid_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (bid_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (offer_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (offer_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (timestamp_value, bytes) =>
                                  Some ({| trader_id := trader_id_value; security_id := security_id_value; bid_quantity := bid_quantity_value; bid_price := bid_price_value; offer_quantity := offer_quantity_value; offer_price := offer_price_value; timestamp := timestamp_value |}, bytes)
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

  End QuoteAddReplaceMessage.

  Module QuoteCancelMessage.

    (** The Quote Cancel message is published when a quote is removed for a particular security. The quote may have been cancelled by the trading Member or by the Aquis support team or the market may have closed. *)
    Record t := {
      trader_id : N;
      security_id : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trader_id record < 256 ^ N.of_nat 2)%N /\
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (trader_id record) ++
      encode_uint 2 (security_id record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  Some ({| trader_id := trader_id_value; security_id := security_id_value; timestamp := timestamp_value |}, bytes)
              end
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

  End QuoteCancelMessage.

  Module SecurityStatisticsMessage.

    (** The Security Statistics message is published to disseminate the opening and closing prices of a security. *)
    Record t := {
      security_id : N;
      statistics_price : N;
      price_type : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (statistics_price record < 256 ^ N.of_nat 8)%N /\
      (price_type record < 256 ^ N.of_nat 1)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 8 (statistics_price record) ++
      encode_uint 1 (price_type record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (statistics_price_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (price_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_value, bytes) =>
                      Some ({| security_id := security_id_value; statistics_price := statistics_price_value; price_type := price_type_value; timestamp := timestamp_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  End SecurityStatisticsMessage.

  Module TraderDefinitionMessage.

    (** A series of Trader Definition messages are published pre-market to identify the quote originators. *)
    Record t := {
      trader_id : N;
      sender_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trader_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (sender_id record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (trader_id record) ++
      encode_bytes 16 (sender_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (trader_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (sender_id_value, bytes) =>
              Some ({| trader_id := trader_id_value; sender_id := sender_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End TraderDefinitionMessage.

  Module TickTableDataMessage.

    (** A series of Tick Table Data messages are published pre-market to specify the dynamic tick tables and static ticks that apply to the securities traded on AQSE. *)
    Record t := {
      tick_table_id : N;
      name : list byte;
      threshold : N;
      tick_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tick_table_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (name record) = 10 /\
      (threshold record < 256 ^ N.of_nat 8)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (tick_table_id record) ++
      encode_bytes 10 (name record) ++
      encode_uint 8 (threshold record) ++
      encode_uint 8 (tick_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (tick_table_id_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (name_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (threshold_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (tick_size_value, bytes) =>
                      Some ({| tick_table_id := tick_table_id_value; name := name_value; threshold := threshold_value; tick_size := tick_size_value |}, bytes)
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

  End TickTableDataMessage.

  Module SecurityDefinitionMessage.

    (** A series of Security Definition messages are published pre-market to identify the securities traded on AQSE (those relevant to the particular feed e.g. Euronext securities). *)
    Record t := {
      security_id : N;
      umtf : list byte;
      isin : list byte;
      currency : list byte;
      mic : list byte;
      tick_table_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (umtf record) = 6 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (mic record) = 4 /\
      (tick_table_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_bytes 6 (umtf record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 4 (mic record) ++
      encode_uint 1 (tick_table_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (umtf_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (currency_value, bytes) =>
                      match decode_bytes 4 bytes with
                      | None => None
                      | Some (mic_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (tick_table_id_value, bytes) =>
                              Some ({| security_id := security_id_value; umtf := umtf_value; isin := isin_value; currency := currency_value; mic := mic_value; tick_table_id := tick_table_id_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SecurityDefinitionMessage.

  Module AodUpdateMessage.

    (** During the AoD this message is used to publish the indicative price and indicative matched volume. The first AoD update message signals the start of an auction. *)
    Record t := {
      security_id : N;
      indicative_price : N;
      match_vol : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (match_vol record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 4 (match_vol record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (indicative_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (match_vol_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_value, bytes) =>
                      Some ({| security_id := security_id_value; indicative_price := indicative_price_value; match_vol := match_vol_value; timestamp := timestamp_value |}, bytes)
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

  End AodUpdateMessage.

End AquisStockExchangeRealTimeV123.
