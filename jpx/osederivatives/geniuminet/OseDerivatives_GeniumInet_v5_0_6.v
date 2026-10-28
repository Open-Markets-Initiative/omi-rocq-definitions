From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Japan Exchange Group Genium Inet

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
      - a field read in bits
  *)

Module OseDerivativesGeniumInetV506.

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

    (** Sent every second for which at least one ITCH message is being generated *)
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

  End SecondsMessage.

  Module OrderBookDirectory.

    (** Disseminated for all active securities at start of day or intra-day. *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      symbol : list byte;
      long_name : list byte;
      isin : list byte;
      financial_product : N;
      trading_currency : list byte;
      decimals_in_price : N;
      decimals_in_nominal_value : N;
      odd_lot_size : N;
      round_lot_size : N;
      block_lot_size : N;
      nominal_value : N;
      number_of_legs : N;
      underlying_orderbook_id : N;
      strike_price : N;
      expiration_date : N;
      decimals_in_strike_price : N;
      put_or_call : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 32 /\
      Datatypes.length (long_name record) = 32 /\
      Datatypes.length (isin record) = 12 /\
      (financial_product record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_currency record) = 3 /\
      (decimals_in_price record < 256 ^ N.of_nat 2)%N /\
      (decimals_in_nominal_value record < 256 ^ N.of_nat 2)%N /\
      (odd_lot_size record < 256 ^ N.of_nat 4)%N /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      (block_lot_size record < 256 ^ N.of_nat 4)%N /\
      (nominal_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_legs record < 256 ^ N.of_nat 1)%N /\
      (underlying_orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (expiration_date record < 256 ^ N.of_nat 4)%N /\
      (decimals_in_strike_price record < 256 ^ N.of_nat 2)%N /\
      (put_or_call record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 32 (symbol record) ++
      encode_bytes 32 (long_name record) ++
      encode_bytes 12 (isin record) ++
      encode_uint 1 (financial_product record) ++
      encode_bytes 3 (trading_currency record) ++
      encode_uint 2 (decimals_in_price record) ++
      encode_uint 2 (decimals_in_nominal_value record) ++
      encode_uint 4 (odd_lot_size record) ++
      encode_uint 4 (round_lot_size record) ++
      encode_uint 4 (block_lot_size record) ++
      encode_uint 8 (nominal_value record) ++
      encode_uint 1 (number_of_legs record) ++
      encode_uint 4 (underlying_orderbook_id record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 4 (expiration_date record) ++
      encode_uint 2 (decimals_in_strike_price record) ++
      encode_uint 1 (put_or_call record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
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
                                  | Some (decimals_in_price_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (decimals_in_nominal_value_value, bytes) =>
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
                                                              | Some (underlying_orderbook_id_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (strike_price_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (expiration_date_value, bytes) =>
                                                                          match decode_uint 2 bytes with
                                                                          | None => None
                                                                          | Some (decimals_in_strike_price_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (put_or_call_value, bytes) =>
                                                                                  Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; symbol := symbol_value; long_name := long_name_value; isin := isin_value; financial_product := financial_product_value; trading_currency := trading_currency_value; decimals_in_price := decimals_in_price_value; decimals_in_nominal_value := decimals_in_nominal_value_value; odd_lot_size := odd_lot_size_value; round_lot_size := round_lot_size_value; block_lot_size := block_lot_size_value; nominal_value := nominal_value_value; number_of_legs := number_of_legs_value; underlying_orderbook_id := underlying_orderbook_id_value; strike_price := strike_price_value; expiration_date := expiration_date_value; decimals_in_strike_price := decimals_in_strike_price_value; put_or_call := put_or_call_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 128.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookDirectory.

  Module CombinationOrderbookLeg.

    (** Mapping between a combination orderbook and its leg orderbooks. *)
    Record t := {
      nanoseconds : N;
      combination_orderbook_id : N;
      leg_orderbook_id : N;
      leg_side : list byte;
      leg_ratio : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (combination_orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (leg_orderbook_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_side record) = 1 /\
      (leg_ratio record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (combination_orderbook_id record) ++
      encode_uint 4 (leg_orderbook_id record) ++
      encode_bytes 1 (leg_side record) ++
      encode_uint 4 (leg_ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (combination_orderbook_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (leg_orderbook_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (leg_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (leg_ratio_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; combination_orderbook_id := combination_orderbook_id_value; leg_orderbook_id := leg_orderbook_id_value; leg_side := leg_side_value; leg_ratio := leg_ratio_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CombinationOrderbookLeg.

  Module TickSizeTableEntry.

    (** Information on a tick size for a price range. *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      tick_size : N;
      price_from : N;
      price_to : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N /\
      (price_from record < 256 ^ N.of_nat 4)%N /\
      (price_to record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (tick_size record) ++
      encode_uint 4 (price_from record) ++
      encode_uint 4 (price_to record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
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
                          Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; tick_size := tick_size_value; price_from := price_from_value; price_to := price_to_value |}, bytes)
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

    (** Signals a market or data feed handler event. *)
    Record t := {
      nanoseconds : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              Some ({| nanoseconds := nanoseconds_value; event_code := event_code_value |}, bytes)
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

    (** Relays information on state changes. *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      state_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (state_name record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 20 (state_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 20 bytes with
              | None => None
              | Some (state_name_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; state_name := state_name_value |}, bytes)
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

  Module OrderExecutedMessage.

    (** Sent whenever an order on the book is executed in whole or in part. *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
      executed_quantity : N;
      match_id : N;
      combo_group_id : N;
      participant_id_owner : list byte;
      participant_id_counterparty : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (participant_id_owner record) = 7 /\
      Datatypes.length (participant_id_counterparty record) = 7.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_bytes 7 (participant_id_owner record) ++
      encode_bytes 7 (participant_id_counterparty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (executed_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (combo_group_id_value, bytes) =>
                                  match decode_bytes 7 bytes with
                                  | None => None
                                  | Some (participant_id_owner_value, bytes) =>
                                      match decode_bytes 7 bytes with
                                      | None => None
                                      | Some (participant_id_counterparty_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value; executed_quantity := executed_quantity_value; match_id := match_id_value; combo_group_id := combo_group_id_value; participant_id_owner := participant_id_owner_value; participant_id_counterparty := participant_id_counterparty_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** Sent when an order is executed at a price different than the initial display price. *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
      executed_quantity : N;
      match_id : N;
      combo_group_id : N;
      owner_participant_id : list byte;
      counterparty_participant_id : list byte;
      trade_price : N;
      occurred_at_cross : list byte;
      printable : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (owner_participant_id record) = 7 /\
      Datatypes.length (counterparty_participant_id record) = 7 /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (occurred_at_cross record) = 1 /\
      Datatypes.length (printable record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_bytes 7 (owner_participant_id record) ++
      encode_bytes 7 (counterparty_participant_id record) ++
      encode_uint 4 (trade_price record) ++
      encode_bytes 1 (occurred_at_cross record) ++
      encode_bytes 1 (printable record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (executed_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (combo_group_id_value, bytes) =>
                                  match decode_bytes 7 bytes with
                                  | None => None
                                  | Some (owner_participant_id_value, bytes) =>
                                      match decode_bytes 7 bytes with
                                      | None => None
                                      | Some (counterparty_participant_id_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_price_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (occurred_at_cross_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (printable_value, bytes) =>
                                                      Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value; executed_quantity := executed_quantity_value; match_id := match_id_value; combo_group_id := combo_group_id_value; owner_participant_id := owner_participant_id_value; counterparty_participant_id := counterparty_participant_id_value; trade_price := trade_price_value; occurred_at_cross := occurred_at_cross_value; printable := printable_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceMessage.

  Module OrderDeleteMessage.

    (** Sent whenever an order on the book is being deleted. There will be no remaining quantity. *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderDeleteMessage.

  Module TradeMessage.

    (** Execution details for normal match events involving non-displayable order types or cross trades. *)
    Record t := {
      nanoseconds : N;
      match_id : N;
      combo_group_id : N;
      side : list byte;
      quantity : N;
      order_book_id : N;
      trade_price : N;
      owner_participant_id : list byte;
      counterparty_participant_id : list byte;
      printable : list byte;
      occurred_at_cross : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (owner_participant_id record) = 7 /\
      Datatypes.length (counterparty_participant_id record) = 7 /\
      Datatypes.length (printable record) = 1 /\
      Datatypes.length (occurred_at_cross record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (match_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 4 (trade_price record) ++
      encode_bytes 7 (owner_participant_id record) ++
      encode_bytes 7 (counterparty_participant_id record) ++
      encode_bytes 1 (printable record) ++
      encode_bytes 1 (occurred_at_cross record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (match_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (combo_group_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_id_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (trade_price_value, bytes) =>
                                  match decode_bytes 7 bytes with
                                  | None => None
                                  | Some (owner_participant_id_value, bytes) =>
                                      match decode_bytes 7 bytes with
                                      | None => None
                                      | Some (counterparty_participant_id_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (printable_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (occurred_at_cross_value, bytes) =>
                                                  Some ({| nanoseconds := nanoseconds_value; match_id := match_id_value; combo_group_id := combo_group_id_value; side := side_value; quantity := quantity_value; order_book_id := order_book_id_value; trade_price := trade_price_value; owner_participant_id := owner_participant_id_value; counterparty_participant_id := counterparty_participant_id_value; printable := printable_value; occurred_at_cross := occurred_at_cross_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module EquilibriumPriceUpdate.

    (** Provides changes in equilibrium price during auctions. *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      available_bid_quantity_at_equilibrium_price : N;
      available_ask_quantity_at_equilibrium_price : N;
      equilibrium_price : N;
      reserved_24 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (available_bid_quantity_at_equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (available_ask_quantity_at_equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (equilibrium_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_24 record) = 24.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (available_bid_quantity_at_equilibrium_price record) ++
      encode_uint 8 (available_ask_quantity_at_equilibrium_price record) ++
      encode_uint 4 (equilibrium_price record) ++
      encode_bytes 24 (reserved_24 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (available_bid_quantity_at_equilibrium_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (available_ask_quantity_at_equilibrium_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (equilibrium_price_value, bytes) =>
                          match decode_bytes 24 bytes with
                          | None => None
                          | Some (reserved_24_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; available_bid_quantity_at_equilibrium_price := available_bid_quantity_at_equilibrium_price_value; available_ask_quantity_at_equilibrium_price := available_ask_quantity_at_equilibrium_price_value; equilibrium_price := equilibrium_price_value; reserved_24 := reserved_24_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EquilibriumPriceUpdate.

End OseDerivativesGeniumInetV506.
