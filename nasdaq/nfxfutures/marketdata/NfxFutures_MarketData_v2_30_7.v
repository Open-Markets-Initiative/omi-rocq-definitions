From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Genium INET Auxiliary Market Data

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
      - a run counted by a field
  *)

Module NfxFuturesMarketDataV2307.

  Module PacketHeader.

    (** Itch Mold Udp 64 Packet Header *)
    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module MessageHeader.

    (** Mold Udp 64 Message Header *)
    Record t := {
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End MessageHeader.

  Module SecondsMessage.

    Record t := {
      second : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (second record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (second record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (second_value, bytes) =>
          Some ({| second := second_value |}, bytes)
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

  End SecondsMessage.

  Module OrderBookDirectory.

    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      symbol : list byte;
      long_name : list byte;
      isin : list byte;
      financial_product : N;
      trading_currency : list byte;
      number_of_decimals_in_price : N;
      number_of_decimals_in_nominal_value : N;
      odd_lot_size : N;
      round_lot_size : N;
      block_lot_size : N;
      nominal_value : N;
      number_of_legs : N;
      underlying_order_book_id : N;
      strike_price : N;
      expiration_date : N;
      number_of_decimals_in_strike_price : N;
      put_or_call : N;
      market_id : N;
      strategy_subtype : N;
      minimum_quantity_and_multiple : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 32 /\
      Datatypes.length (long_name record) = 32 /\
      Datatypes.length (isin record) = 12 /\
      (financial_product record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_currency record) = 3 /\
      (number_of_decimals_in_price record < 256 ^ N.of_nat 2)%N /\
      (number_of_decimals_in_nominal_value record < 256 ^ N.of_nat 2)%N /\
      (odd_lot_size record < 256 ^ N.of_nat 4)%N /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      (block_lot_size record < 256 ^ N.of_nat 4)%N /\
      (nominal_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_legs record < 256 ^ N.of_nat 1)%N /\
      (underlying_order_book_id record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (expiration_date record < 256 ^ N.of_nat 4)%N /\
      (number_of_decimals_in_strike_price record < 256 ^ N.of_nat 2)%N /\
      (put_or_call record < 256 ^ N.of_nat 1)%N /\
      (market_id record < 256 ^ N.of_nat 2)%N /\
      (strategy_subtype record < 256 ^ N.of_nat 1)%N /\
      (minimum_quantity_and_multiple record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 32 (symbol record) ++
      encode_bytes 32 (long_name record) ++
      encode_bytes 12 (isin record) ++
      encode_uint 1 (financial_product record) ++
      encode_bytes 3 (trading_currency record) ++
      encode_uint 2 (number_of_decimals_in_price record) ++
      encode_uint 2 (number_of_decimals_in_nominal_value record) ++
      encode_uint 4 (odd_lot_size record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_uint 4 (block_lot_size record) ++
      encode_uint 8 (nominal_value record) ++
      encode_uint 1 (number_of_legs record) ++
      encode_uint 4 (underlying_order_book_id record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 4 (expiration_date record) ++
      encode_uint 2 (number_of_decimals_in_strike_price record) ++
      encode_uint 1 (put_or_call record) ++
      encode_uint 2 (market_id record) ++
      encode_uint 1 (strategy_subtype record) ++
      encode_uint 4 (minimum_quantity_and_multiple record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (long_name_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (isin_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (financial_product_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (trading_currency_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (number_of_decimals_in_price_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (number_of_decimals_in_nominal_value_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (odd_lot_size_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (round_lot_size_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (block_lot_size_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (nominal_value_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (number_of_legs_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (underlying_order_book_id_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (strike_price_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (expiration_date_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (number_of_decimals_in_strike_price_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (put_or_call_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (market_id_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (strategy_subtype_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (minimum_quantity_and_multiple_value, bytes) =>
                                                                                              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; symbol := symbol_value; long_name := long_name_value; isin := isin_value; financial_product := financial_product_value; trading_currency := trading_currency_value; number_of_decimals_in_price := number_of_decimals_in_price_value; number_of_decimals_in_nominal_value := number_of_decimals_in_nominal_value_value; odd_lot_size := odd_lot_size_value; round_lot_size := round_lot_size_value; block_lot_size := block_lot_size_value; nominal_value := nominal_value_value; number_of_legs := number_of_legs_value; underlying_order_book_id := underlying_order_book_id_value; strike_price := strike_price_value; expiration_date := expiration_date_value; number_of_decimals_in_strike_price := number_of_decimals_in_strike_price_value; put_or_call := put_or_call_value; market_id := market_id_value; strategy_subtype := strategy_subtype_value; minimum_quantity_and_multiple := minimum_quantity_and_multiple_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 135.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookDirectory.

  Module CombinationOrderBookLeg.

    (** Combination Order book Directory Message *)
    Record t := {
      timestamp_nanoseconds : N;
      combination_order_book_id : N;
      leg_order_book_id : N;
      leg_side : list byte;
      leg_ratio : N;
      leg_price_future : N;
      leg_delta : N;
      leg_quantity_future : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (combination_order_book_id record < 256 ^ N.of_nat 4)%N /\
      (leg_order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side record) = 1 /\
      (leg_ratio record < 256 ^ N.of_nat 4)%N /\
      (leg_price_future record < 256 ^ N.of_nat 4)%N /\
      (leg_delta record < 256 ^ N.of_nat 4)%N /\
      (leg_quantity_future record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (combination_order_book_id record) ++
      encode_uint 4 (leg_order_book_id record) ++
      encode_bytes 1 (leg_side record) ++
      encode_uint 4 (leg_ratio record) ++
      encode_uint 4 (leg_price_future record) ++
      encode_uint 4 (leg_delta record) ++
      encode_uint 4 (leg_quantity_future record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (combination_order_book_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (leg_order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (leg_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (leg_ratio_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (leg_price_future_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (leg_delta_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (leg_quantity_future_value, bytes) =>
                                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; combination_order_book_id := combination_order_book_id_value; leg_order_book_id := leg_order_book_id_value; leg_side := leg_side_value; leg_ratio := leg_ratio_value; leg_price_future := leg_price_future_value; leg_delta := leg_delta_value; leg_quantity_future := leg_quantity_future_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CombinationOrderBookLeg.

  Module TickSizeTableEntry.

    (** L - Tick Size Message. *)
    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      tick_size : N;
      price_from : N;
      price_to : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N /\
      (price_from record < 256 ^ N.of_nat 4)%N /\
      (price_to record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (tick_size record) ++
      encode_uint 4 (price_from record) ++
      encode_uint 4 (price_to record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tick_size_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_from_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_to_value, bytes) =>
                          Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; tick_size := tick_size_value; price_from := price_from_value; price_to := price_to_value |}, bytes)
                      end
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

  End TickSizeTableEntry.

  Module SystemEventMessage.

    Record t := {
      timestamp_nanoseconds : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; event_code := event_code_value |}, bytes)
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

  Module OrderBookStateMessage.

    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      state_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (state_name record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 20 (state_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (state_name_value, bytes) =>
                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; state_name := state_name_value |}, bytes)
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

  End OrderBookStateMessage.

  Module ReportedTrade.

    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      traded_quantity : N;
      match_id : N;
      combo_group_id : N;
      time_of_trade_execution : N;
      time_of_trade_agreement : N;
      time_of_trade_dissemination : N;
      trade_price : N;
      trade_type : N;
      reserved : list byte;
      second_reserved : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (traded_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      (time_of_trade_execution record < 256 ^ N.of_nat 8)%N /\
      (time_of_trade_agreement record < 256 ^ N.of_nat 8)%N /\
      (time_of_trade_dissemination record < 256 ^ N.of_nat 8)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (trade_type record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (reserved record) = 7 /\
      Datatypes.length (second_reserved record) = 7.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (traded_quantity record) ++
      encode_uint 8 (match_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_uint 8 (time_of_trade_execution record) ++
      encode_uint 8 (time_of_trade_agreement record) ++
      encode_uint 8 (time_of_trade_dissemination record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 2 (trade_type record) ++
      encode_bytes 7 (reserved record) ++
      encode_bytes 7 (second_reserved record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (traded_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (combo_group_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (time_of_trade_execution_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (time_of_trade_agreement_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (time_of_trade_dissemination_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (trade_type_value, bytes) =>
                                              match decode_bytes 7 bytes with
                                              | None => None
                                              | Some (reserved_value, bytes) =>
                                                  match decode_bytes 7 bytes with
                                                  | None => None
                                                  | Some (second_reserved_value, bytes) =>
                                                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; traded_quantity := traded_quantity_value; match_id := match_id_value; combo_group_id := combo_group_id_value; time_of_trade_execution := time_of_trade_execution_value; time_of_trade_agreement := time_of_trade_agreement_value; time_of_trade_dissemination := time_of_trade_dissemination_value; trade_price := trade_price_value; trade_type := trade_type_value; reserved := reserved_value; second_reserved := second_reserved_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
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
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReportedTrade.

  Module BrokenTradeMessage.

    Record t := {
      timestamp_nanoseconds : N;
      match_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 8 (match_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (match_id_value, bytes) =>
              Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; match_id := match_id_value |}, bytes)
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

  End BrokenTradeMessage.

  Module OpenInterestMessage.

    Record t := {
      timestamp_nanoseconds : N;
      order_book_id : N;
      open_interest : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (open_interest record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (open_interest_value, bytes) =>
                  Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; order_book_id := order_book_id_value; open_interest := open_interest_value |}, bytes)
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

  End OpenInterestMessage.

  Module PriceMessage.

    Record t := {
      timestamp_nanoseconds : N;
      price_type : list byte;
      order_book_id : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp_nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_type record) = 1 /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp_nanoseconds record) ++
      encode_bytes 1 (price_type record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      Some ({| timestamp_nanoseconds := timestamp_nanoseconds_value; price_type := price_type_value; order_book_id := order_book_id_value; price := price_value |}, bytes)
                  end
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

  End PriceMessage.

End NfxFuturesMarketDataV2307.
