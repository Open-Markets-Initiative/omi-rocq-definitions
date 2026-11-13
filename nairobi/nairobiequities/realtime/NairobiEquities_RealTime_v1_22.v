From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Nairobi Securities Exchange Nairobi Equities Real Time

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

Module NairobiEquitiesRealTimeV122.

  Module UnitHeader.

    (** Nairobi Mitch Udp Unit Header *)
    Record t := {
      length_ : N;
      message_count : N;
      market_data_group : list byte;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_data_group record) = 1 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_bytes 1 (market_data_group record) ++
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; market_data_group := market_data_group_value; sequence_number := sequence_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnitHeader.

  Module MessageHeader.

    (** Nairobi Mitch Udp Message Header *)
    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

    (** Sent by the server for every second for which at least one application message is generated; its time is the reference for the nanosecond offsets of every other application message. *)
    Record t := {
      seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          Some ({| seconds := seconds_value |}, bytes)
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

  Module SystemEventMessage.

    (** Sent to indicate the start and end of the day. *)
    Record t := {
      nanosecond : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              Some ({| nanosecond := nanosecond_value; event_code := event_code_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End SystemEventMessage.

  Module OrderDeletedMessage.

    (** Sent to indicate that the remainder of a displayed order is cancelled. *)
    Record t := {
      nanosecond : N;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              Some ({| nanosecond := nanosecond_value; order_id := order_id_value |}, bytes)
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

  End OrderDeletedMessage.

  Module OrderBookClearMessage.

    (** Sent to instruct recipients to remove all orders from the order book for the specified instrument. *)
    Record t := {
      nanosecond : N;
      symbol : list byte;
      sub_book : N;
      book_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (sub_book record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (book_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 1 (sub_book record) ++
      encode_bytes 1 (book_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (sub_book_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (book_type_value, bytes) =>
                      Some ({| nanosecond := nanosecond_value; symbol := symbol_value; sub_book := sub_book_value; book_type := book_type_value |}, bytes)
                  end
              end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookClearMessage.

  Module OrderExecutedMessage.

    (** Indicates that the displayed portion of an order is fully or partially filled at its displayed price. The executed quantity is included in the message. *)
    Record t := {
      nanosecond : N;
      order_id : N;
      executed_quantity : N;
      trade_id : N;
      buy_firm : list byte;
      sell_firm : list byte;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy_firm record) = 6 /\
      Datatypes.length (sell_firm record) = 6 /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 6 (buy_firm record) ++
      encode_bytes 6 (sell_firm record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (buy_firm_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (sell_firm_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (last_opt_px_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (volatility_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (underlying_reference_price_value, bytes) =>
                                          Some ({| nanosecond := nanosecond_value; order_id := order_id_value; executed_quantity := executed_quantity_value; trade_id := trade_id_value; buy_firm := buy_firm_value; sell_firm := sell_firm_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
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
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceSizeMessage.

    (** Sent if a displayed order is fully or partially filled at a price that is different from its displayed price, with an indication of whether the trade should update time and sales and statistics displays. *)
    Record t := {
      nanosecond : N;
      order_id : N;
      executed_quantity : N;
      display_quantity : N;
      trade_id : N;
      printable : list byte;
      price : N;
      buy_firm : list byte;
      sell_firm : list byte;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (display_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (printable record) = 1 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buy_firm record) = 6 /\
      Datatypes.length (sell_firm record) = 6 /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (display_quantity record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (price record) ++
      encode_bytes 6 (buy_firm record) ++
      encode_bytes 6 (sell_firm record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (display_quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (printable_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (buy_firm_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (sell_firm_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (last_opt_px_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (volatility_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (underlying_reference_price_value, bytes) =>
                                                      Some ({| nanosecond := nanosecond_value; order_id := order_id_value; executed_quantity := executed_quantity_value; display_quantity := display_quantity_value; trade_id := trade_id_value; printable := printable_value; price := price_value; buy_firm := buy_firm_value; sell_firm := sell_firm_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceSizeMessage.

  Module TradeMessage.

    (** Sent if the non-displayed portion of an iceberg order or a reserve order is fully or partially filled, or if the negotiated non-disclosed order in the block trade order book is executed. *)
    Record t := {
      nanosecond : N;
      executed_quantity : N;
      symbol : list byte;
      price : N;
      trade_id : N;
      sub_book : N;
      buy_firm : list byte;
      sell_firm : list byte;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (sub_book record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_firm record) = 6 /\
      Datatypes.length (sell_firm record) = 6 /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 1 (sub_book record) ++
      encode_bytes 6 (buy_firm record) ++
      encode_bytes 6 (sell_firm record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (sub_book_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (buy_firm_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (sell_firm_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_opt_px_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (volatility_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (underlying_reference_price_value, bytes) =>
                                                  Some ({| nanosecond := nanosecond_value; executed_quantity := executed_quantity_value; symbol := symbol_value; price := price_value; trade_id := trade_id_value; sub_book := sub_book_value; buy_firm := buy_firm_value; sell_firm := sell_firm_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module AuctionTradeMessage.

    (** Sent to report details of an auction (e.g. opening, closing, intra-day, etc.). *)
    Record t := {
      nanosecond : N;
      executed_quantity : N;
      symbol : list byte;
      price : N;
      trade_id : N;
      auction_type : list byte;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (auction_type_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (last_opt_px_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (volatility_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (underlying_reference_price_value, bytes) =>
                                          Some ({| nanosecond := nanosecond_value; executed_quantity := executed_quantity_value; symbol := symbol_value; price := price_value; trade_id := trade_id_value; auction_type := auction_type_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionTradeMessage.

  Module OffBookTradeMessage.

    (** Sent to report the details of an off-book trade. *)
    Record t := {
      nanosecond : N;
      executed_quantity : N;
      symbol : list byte;
      price : N;
      trade_id : N;
      off_book_trade_type : list byte;
      trade_time : list byte;
      trade_date : list byte;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (off_book_trade_type record) = 4 /\
      Datatypes.length (trade_time record) = 8 /\
      Datatypes.length (trade_date record) = 8 /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 4 (off_book_trade_type record) ++
      encode_bytes 8 (trade_time record) ++
      encode_bytes 8 (trade_date record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (off_book_trade_type_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (trade_time_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (trade_date_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_opt_px_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (volatility_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (underlying_reference_price_value, bytes) =>
                                                  Some ({| nanosecond := nanosecond_value; executed_quantity := executed_quantity_value; symbol := symbol_value; price := price_value; trade_id := trade_id_value; off_book_trade_type := off_book_trade_type_value; trade_time := trade_time_value; trade_date := trade_date_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 76.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OffBookTradeMessage.

  Module TradeBreakMessage.

    (** Sent to indicate that a previously reported trade is cancelled. *)
    Record t := {
      nanosecond : N;
      trade_id : N;
      trade_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 1 (trade_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trade_type_value, bytes) =>
                  Some ({| nanosecond := nanosecond_value; trade_id := trade_id_value; trade_type := trade_type_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeBreakMessage.

  Module TradeCorrectionMessage.

    (** Sent to report the correction of the executed quantity of a trade. *)
    Record t := {
      nanosecond : N;
      trade_id : N;
      symbol : list byte;
      price : N;
      quantity : N;
      sub_book : N;
      buy_firm : list byte;
      sell_firm : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (sub_book record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_firm record) = 6 /\
      Datatypes.length (sell_firm record) = 6.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 1 (sub_book record) ++
      encode_bytes 6 (buy_firm record) ++
      encode_bytes 6 (sell_firm record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_id_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (sub_book_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (buy_firm_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (sell_firm_value, bytes) =>
                                      Some ({| nanosecond := nanosecond_value; trade_id := trade_id_value; symbol := symbol_value; price := price_value; quantity := quantity_value; sub_book := sub_book_value; buy_firm := buy_firm_value; sell_firm := sell_firm_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeCorrectionMessage.

  Module RecoveryTradeMessage.

    (** Sent on the Snapshot channel to retransmit the trades published on the Real-Time channel. *)
    Record t := {
      nanosecond : N;
      executed_quantity : N;
      symbol : list byte;
      price : N;
      trade_id : N;
      auction_type : list byte;
      off_book_trade_type : list byte;
      trade_time : list byte;
      trade_date : list byte;
      action_type : list byte;
      sub_book : N;
      buy_firm : list byte;
      sell_firm : list byte;
      last_opt_px : N;
      volatility : N;
      underlying_reference_price : N;
      auction_trade_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (off_book_trade_type record) = 4 /\
      Datatypes.length (trade_time record) = 8 /\
      Datatypes.length (trade_date record) = 8 /\
      Datatypes.length (action_type record) = 1 /\
      (sub_book record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_firm record) = 6 /\
      Datatypes.length (sell_firm record) = 6 /\
      (last_opt_px record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (underlying_reference_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_trade_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (trade_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 4 (off_book_trade_type record) ++
      encode_bytes 8 (trade_time record) ++
      encode_bytes 8 (trade_date record) ++
      encode_bytes 1 (action_type record) ++
      encode_uint 1 (sub_book record) ++
      encode_bytes 6 (buy_firm record) ++
      encode_bytes 6 (sell_firm record) ++
      encode_uint 8 (last_opt_px record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (underlying_reference_price record) ++
      encode_bytes 1 (auction_trade_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (auction_type_value, bytes) =>
                              match decode_bytes 4 bytes with
                              | None => None
                              | Some (off_book_trade_type_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (trade_time_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (trade_date_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (action_type_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (sub_book_value, bytes) =>
                                                  match decode_bytes 6 bytes with
                                                  | None => None
                                                  | Some (buy_firm_value, bytes) =>
                                                      match decode_bytes 6 bytes with
                                                      | None => None
                                                      | Some (sell_firm_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (last_opt_px_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (volatility_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (underlying_reference_price_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (auction_trade_type_value, bytes) =>
                                                                          Some ({| nanosecond := nanosecond_value; executed_quantity := executed_quantity_value; symbol := symbol_value; price := price_value; trade_id := trade_id_value; auction_type := auction_type_value; off_book_trade_type := off_book_trade_type_value; trade_time := trade_time_value; trade_date := trade_date_value; action_type := action_type_value; sub_book := sub_book_value; buy_firm := buy_firm_value; sell_firm := sell_firm_value; last_opt_px := last_opt_px_value; volatility := volatility_value; underlying_reference_price := underlying_reference_price_value; auction_trade_type := auction_trade_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 92.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RecoveryTradeMessage.

  Module AuctionInfoMessage.

    (** Indicative auction information for an instrument; the document labels the message type Indicative Auction Info. *)
    Record t := {
      nanosecond : N;
      paired_quantity : N;
      imbalance_quantity : N;
      imbalance_direction : list byte;
      symbol : list byte;
      price : N;
      auction_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (paired_quantity record < 256 ^ N.of_nat 4)%N /\
      (imbalance_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (imbalance_direction record) = 1 /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 4 (paired_quantity record) ++
      encode_uint 4 (imbalance_quantity record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (auction_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (paired_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (imbalance_quantity_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (imbalance_direction_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (auction_type_value, bytes) =>
                                  Some ({| nanosecond := nanosecond_value; paired_quantity := paired_quantity_value; imbalance_quantity := imbalance_quantity_value; imbalance_direction := imbalance_direction_value; symbol := symbol_value; price := price_value; auction_type := auction_type_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionInfoMessage.

  Module StatisticsMessage.

    (** Sent to disseminate the opening, closing and previous closing prices of an instrument. *)
    Record t := {
      nanosecond : N;
      symbol : list byte;
      statistic_type : list byte;
      price : N;
      open_close_indicator : list byte;
      sub_book : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (statistic_type record) = 1 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_close_indicator record) = 1 /\
      (sub_book record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 12 (symbol record) ++
      encode_bytes 1 (statistic_type record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (open_close_indicator record) ++
      encode_uint 1 (sub_book record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (statistic_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (open_close_indicator_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (sub_book_value, bytes) =>
                              Some ({| nanosecond := nanosecond_value; symbol := symbol_value; statistic_type := statistic_type_value; price := price_value; open_close_indicator := open_close_indicator_value; sub_book := sub_book_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatisticsMessage.

  Module ExtendedStatisticsMessage.

    (** Sent to disseminate the high, low, VWAP, volume, turnover and other statistics of an instrument for a sub book. *)
    Record t := {
      nanosecond : N;
      symbol : list byte;
      high_price : N;
      low_price : N;
      vwap : N;
      volume : N;
      turnover : N;
      trades : N;
      reserved_8 : list byte;
      sub_book : N;
      notional_exposure : N;
      notional_delta_exposure : N;
      daily_foreign_buy_value : N;
      daily_foreign_sell_value : N;
      market_capitalization : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (high_price record < 256 ^ N.of_nat 4)%N /\
      (low_price record < 256 ^ N.of_nat 4)%N /\
      (vwap record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (trades record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_8 record) = 8 /\
      (sub_book record < 256 ^ N.of_nat 1)%N /\
      (notional_exposure record < 256 ^ N.of_nat 8)%N /\
      (notional_delta_exposure record < 256 ^ N.of_nat 8)%N /\
      (daily_foreign_buy_value record < 256 ^ N.of_nat 8)%N /\
      (daily_foreign_sell_value record < 256 ^ N.of_nat 8)%N /\
      (market_capitalization record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (high_price record) ++
      encode_uint 4 (low_price record) ++
      encode_uint 4 (vwap record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 4 (trades record) ++
      encode_bytes 8 (reserved_8 record) ++
      encode_uint 1 (sub_book record) ++
      encode_uint 8 (notional_exposure record) ++
      encode_uint 8 (notional_delta_exposure record) ++
      encode_uint 8 (daily_foreign_buy_value record) ++
      encode_uint 8 (daily_foreign_sell_value record) ++
      encode_uint 8 (market_capitalization record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (high_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (low_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (vwap_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (turnover_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (trades_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (reserved_8_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (sub_book_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (notional_exposure_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (notional_delta_exposure_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (daily_foreign_buy_value_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (daily_foreign_sell_value_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (market_capitalization_value, bytes) =>
                                                                  Some ({| nanosecond := nanosecond_value; symbol := symbol_value; high_price := high_price_value; low_price := low_price_value; vwap := vwap_value; volume := volume_value; turnover := turnover_value; trades := trades_value; reserved_8 := reserved_8_value; sub_book := sub_book_value; notional_exposure := notional_exposure_value; notional_delta_exposure := notional_delta_exposure_value; daily_foreign_buy_value := daily_foreign_buy_value_value; daily_foreign_sell_value := daily_foreign_sell_value_value; market_capitalization := market_capitalization_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 93.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExtendedStatisticsMessage.

  Module ConsolidatedStatisticsMessage.

    (** Sent to disseminate the volume, turnover and trades of a market, sector or instrument type. *)
    Record t := {
      nanosecond : N;
      statistics_type : N;
      symbol : list byte;
      volume : N;
      turnover : N;
      trades : N;
      daily_foreign_buy_value : N;
      daily_foreign_sell_value : N;
      market_capitalization : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      (statistics_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (symbol record) = 12 /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (trades record < 256 ^ N.of_nat 4)%N /\
      (daily_foreign_buy_value record < 256 ^ N.of_nat 8)%N /\
      (daily_foreign_sell_value record < 256 ^ N.of_nat 8)%N /\
      (market_capitalization record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_uint 1 (statistics_type record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 4 (trades record) ++
      encode_uint 8 (daily_foreign_buy_value record) ++
      encode_uint 8 (daily_foreign_sell_value record) ++
      encode_uint 8 (market_capitalization record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (statistics_type_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (turnover_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trades_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (daily_foreign_buy_value_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (daily_foreign_sell_value_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (market_capitalization_value, bytes) =>
                                          Some ({| nanosecond := nanosecond_value; statistics_type := statistics_type_value; symbol := symbol_value; volume := volume_value; turnover := turnover_value; trades := trades_value; daily_foreign_buy_value := daily_foreign_buy_value_value; daily_foreign_sell_value := daily_foreign_sell_value_value; market_capitalization := market_capitalization_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
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
      rewrite decode_encode_bytes by exact bound_2.
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

  End ConsolidatedStatisticsMessage.

  Module IndexMessage.

    (** Sent to disseminate the value of an index. *)
    Record t := {
      nanosecond : N;
      symbol : list byte;
      index_value : N;
      update_type : N;
      perctg_diff_from_closing : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (index_value record < 256 ^ N.of_nat 4)%N /\
      (update_type record < 256 ^ N.of_nat 1)%N /\
      (perctg_diff_from_closing record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (index_value record) ++
      encode_uint 1 (update_type record) ++
      encode_uint 4 (perctg_diff_from_closing record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (index_value_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (update_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (perctg_diff_from_closing_value, bytes) =>
                          Some ({| nanosecond := nanosecond_value; symbol := symbol_value; index_value := index_value_value; update_type := update_type_value; perctg_diff_from_closing := perctg_diff_from_closing_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndexMessage.

  Module AonInfoMessage.

    (** Sent to disseminate the details of an All or None auction. *)
    Record t := {
      nanosecond : N;
      symbol : list byte;
      price : N;
      side : list byte;
      quantity : N;
      aon_status : list byte;
      date : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (aon_status record) = 1 /\
      Datatypes.length (date record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 1 (aon_status record) ++
      encode_bytes 8 (date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (aon_status_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (date_value, bytes) =>
                                  Some ({| nanosecond := nanosecond_value; symbol := symbol_value; price := price_value; side := side_value; quantity := quantity_value; aon_status := aon_status_value; date := date_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AonInfoMessage.

  Module NewsMessage.

    (** Sent to disseminate an announcement. *)
    Record t := {
      nanosecond : N;
      time : list byte;
      urgency : list byte;
      headline : list byte;
      text : list byte;
      instruments : list byte;
      underlyings : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time record) = 8 /\
      Datatypes.length (urgency record) = 1 /\
      Datatypes.length (headline record) = 100 /\
      Datatypes.length (text record) = 750 /\
      Datatypes.length (instruments record) = 100 /\
      Datatypes.length (underlyings record) = 100.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanosecond record) ++
      encode_bytes 8 (time record) ++
      encode_bytes 1 (urgency record) ++
      encode_bytes 100 (headline record) ++
      encode_bytes 750 (text record) ++
      encode_bytes 100 (instruments record) ++
      encode_bytes 100 (underlyings record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (time_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (urgency_value, bytes) =>
                  match decode_bytes 100 bytes with
                  | None => None
                  | Some (headline_value, bytes) =>
                      match decode_bytes 750 bytes with
                      | None => None
                      | Some (text_value, bytes) =>
                          match decode_bytes 100 bytes with
                          | None => None
                          | Some (instruments_value, bytes) =>
                              match decode_bytes 100 bytes with
                              | None => None
                              | Some (underlyings_value, bytes) =>
                                  Some ({| nanosecond := nanosecond_value; time := time_value; urgency := urgency_value; headline := headline_value; text := text_value; instruments := instruments_value; underlyings := underlyings_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1063.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewsMessage.

End NairobiEquitiesRealTimeV122.
