From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Genium INET Depth Of Book

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

Module NordicDerivativesDepthOfBookV2224.

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

    (** This message is sent every second for which at least one ITCH message is being generated. The message contains the number of seconds since the start of 1970-01-01 00:00:00 UTC, also called Unix Time *)
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

    (** At the start of each trading day, Order book directory messages are disseminated for all active securities, including halted securities, in the Genium INET Trading system. Intra-day transmissions of this message may occur when new order books are added to the system; updates to existing order books may also be represented by intra-day Order book Directory messages *)
    Record t := {
      nanoseconds : N;
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
      (number_of_decimals_in_price record < 256 ^ N.of_nat 2)%N /\
      (number_of_decimals_in_nominal_value record < 256 ^ N.of_nat 2)%N /\
      (odd_lot_size record < 256 ^ N.of_nat 4)%N /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      (block_lot_size record < 256 ^ N.of_nat 4)%N /\
      (nominal_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
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
      encode_uint 8 (nominal_value record).

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
                                                          Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; symbol := symbol_value; long_name := long_name_value; isin := isin_value; financial_product := financial_product_value; trading_currency := trading_currency_value; number_of_decimals_in_price := number_of_decimals_in_price_value; number_of_decimals_in_nominal_value := number_of_decimals_in_nominal_value_value; odd_lot_size := odd_lot_size_value; round_lot_size := round_lot_size_value; block_lot_size := block_lot_size_value; nominal_value := nominal_value_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 112.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderBookDirectory.

  Module CombinationOrderBookDirectory.

    (** Specialized directory message used when Combination order books are traded in the marketplace. It represents both standard combinations defined by the exchange and tailor-made combinations created by members. Intra-day transmissions may occur when new combination order books are added, typically for tailor-made combinations *)
    Record t := {
      nanoseconds : N;
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
      leg_1_symbol : list byte;
      leg_1_side : list byte;
      leg_1_ratio : N;
      leg_2_symbol : list byte;
      leg_2_side : list byte;
      leg_2_ratio : N;
      leg_3_symbol : list byte;
      leg_3_side : list byte;
      leg_3_ratio : N;
      leg_4_symbol : list byte;
      leg_4_side : list byte;
      leg_4_ratio : N;
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
      (number_of_decimals_in_price record < 256 ^ N.of_nat 2)%N /\
      (number_of_decimals_in_nominal_value record < 256 ^ N.of_nat 2)%N /\
      (odd_lot_size record < 256 ^ N.of_nat 4)%N /\
      (round_lot_size record < 256 ^ N.of_nat 4)%N /\
      (block_lot_size record < 256 ^ N.of_nat 4)%N /\
      (nominal_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (leg_1_symbol record) = 32 /\
      Datatypes.length (leg_1_side record) = 1 /\
      (leg_1_ratio record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_2_symbol record) = 32 /\
      Datatypes.length (leg_2_side record) = 1 /\
      (leg_2_ratio record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_3_symbol record) = 32 /\
      Datatypes.length (leg_3_side record) = 1 /\
      (leg_3_ratio record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_4_symbol record) = 32 /\
      Datatypes.length (leg_4_side record) = 1 /\
      (leg_4_ratio record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
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
      encode_bytes 32 (leg_1_symbol record) ++
      encode_bytes 1 (leg_1_side record) ++
      encode_uint 4 (leg_1_ratio record) ++
      encode_bytes 32 (leg_2_symbol record) ++
      encode_bytes 1 (leg_2_side record) ++
      encode_uint 4 (leg_2_ratio record) ++
      encode_bytes 32 (leg_3_symbol record) ++
      encode_bytes 1 (leg_3_side record) ++
      encode_uint 4 (leg_3_ratio record) ++
      encode_bytes 32 (leg_4_symbol record) ++
      encode_bytes 1 (leg_4_side record) ++
      encode_uint 4 (leg_4_ratio record).

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
                                                          match decode_bytes 32 bytes with
                                                          | None => None
                                                          | Some (leg_1_symbol_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (leg_1_side_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (leg_1_ratio_value, bytes) =>
                                                                      match decode_bytes 32 bytes with
                                                                      | None => None
                                                                      | Some (leg_2_symbol_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (leg_2_side_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (leg_2_ratio_value, bytes) =>
                                                                                  match decode_bytes 32 bytes with
                                                                                  | None => None
                                                                                  | Some (leg_3_symbol_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (leg_3_side_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (leg_3_ratio_value, bytes) =>
                                                                                              match decode_bytes 32 bytes with
                                                                                              | None => None
                                                                                              | Some (leg_4_symbol_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (leg_4_side_value, bytes) =>
                                                                                                      match decode_uint 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (leg_4_ratio_value, bytes) =>
                                                                                                          Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; symbol := symbol_value; long_name := long_name_value; isin := isin_value; financial_product := financial_product_value; trading_currency := trading_currency_value; number_of_decimals_in_price := number_of_decimals_in_price_value; number_of_decimals_in_nominal_value := number_of_decimals_in_nominal_value_value; odd_lot_size := odd_lot_size_value; round_lot_size := round_lot_size_value; block_lot_size := block_lot_size_value; nominal_value := nominal_value_value; leg_1_symbol := leg_1_symbol_value; leg_1_side := leg_1_side_value; leg_1_ratio := leg_1_ratio_value; leg_2_symbol := leg_2_symbol_value; leg_2_side := leg_2_side_value; leg_2_ratio := leg_2_ratio_value; leg_3_symbol := leg_3_symbol_value; leg_3_side := leg_3_side_value; leg_3_ratio := leg_3_ratio_value; leg_4_symbol := leg_4_symbol_value; leg_4_side := leg_4_side_value; leg_4_ratio := leg_4_ratio_value |}, bytes)
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
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 260.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 bound_24]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CombinationOrderBookDirectory.

  Module TickSizeTableEntry.

    (** Contains information on a tick size for a price range. Together, all Tick Size messages with the same order book ID form a complete Tick Size Table. The number of decimals in prices are given by the Order Book Directory message for this order book *)
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

    (** The system event message type is used to signal a market or data feed handler event *)
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

    (** The Order book state message relays information on state changes *)
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

  Module StressedMarketMessage.

    (** The Stressed Market Message is sent whenever the Stressed Market state has changed *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      stressed_market : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (stressed_market record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (stressed_market record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (stressed_market_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; stressed_market := stressed_market_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End StressedMarketMessage.

  Module ExceptionalMarketMessage.

    (** The Exceptional Market Message is sent whenever the Exceptional Market state has changed *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      exceptional_market : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exceptional_market record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (exceptional_market record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (exceptional_market_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; exceptional_market := exceptional_market_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End ExceptionalMarketMessage.

  Module OrderExecutedMessage.

    (** Sent whenever an order on the book is executed in whole or in part. Multiple Order Executed Messages on the same order are cumulative *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
      executed_quantity : N;
      match_id : list byte;
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
      Datatypes.length (match_id record) = 12 /\
      Datatypes.length (participant_id_owner record) = 7 /\
      Datatypes.length (participant_id_counterparty record) = 7.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_bytes 12 (match_id record) ++
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
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_bytes 7 bytes with
                              | None => None
                              | Some (participant_id_owner_value, bytes) =>
                                  match decode_bytes 7 bytes with
                                  | None => None
                                  | Some (participant_id_counterparty_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value; executed_quantity := executed_quantity_value; match_id := match_id_value; participant_id_owner := participant_id_owner_value; participant_id_counterparty := participant_id_counterparty_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** Sent in the relatively rare event that an order on the book is executed in whole or in part with a price different than the initial display price. Combination orders on the book that execute are always represented by this message, with the Printable flag set to N *)
    Record t := {
      nanoseconds : N;
      order_id : N;
      order_book_id : N;
      side : list byte;
      executed_quantity : N;
      match_id : list byte;
      participant_id_owner : list byte;
      participant_id_counterparty : list byte;
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
      Datatypes.length (match_id record) = 12 /\
      Datatypes.length (participant_id_owner record) = 7 /\
      Datatypes.length (participant_id_counterparty record) = 7 /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (occurred_at_cross record) = 1 /\
      Datatypes.length (printable record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (order_book_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_bytes 12 (match_id record) ++
      encode_bytes 7 (participant_id_owner record) ++
      encode_bytes 7 (participant_id_counterparty record) ++
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
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (match_id_value, bytes) =>
                              match decode_bytes 7 bytes with
                              | None => None
                              | Some (participant_id_owner_value, bytes) =>
                                  match decode_bytes 7 bytes with
                                  | None => None
                                  | Some (participant_id_counterparty_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (trade_price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (occurred_at_cross_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (printable_value, bytes) =>
                                                  Some ({| nanoseconds := nanoseconds_value; order_id := order_id_value; order_book_id := order_book_id_value; side := side_value; executed_quantity := executed_quantity_value; match_id := match_id_value; participant_id_owner := participant_id_owner_value; participant_id_counterparty := participant_id_counterparty_value; trade_price := trade_price_value; occurred_at_cross := occurred_at_cross_value; printable := printable_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceMessage.

  Module OrderDeleteMessage.

    (** Sent whenever an order on the book is being deleted. Order Deletes are also sent when an order with an undisclosed quantity is fully filled, when orders are suspended due to connection loss, and for all existing orders prior to an auction where market by order dissemination is disabled *)
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

    (** Provides execution details for normal match events involving non-displayable order types, and is also used to publish individual cross trades *)
    Record t := {
      nanoseconds : N;
      match_id : list byte;
      side : list byte;
      quantity : N;
      order_book_id : N;
      trade_price : N;
      participant_id_owner : list byte;
      participant_id_counterparty : list byte;
      printable : list byte;
      occurred_at_cross : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (match_id record) = 12 /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (participant_id_owner record) = 7 /\
      Datatypes.length (participant_id_counterparty record) = 7 /\
      Datatypes.length (printable record) = 1 /\
      Datatypes.length (occurred_at_cross record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 12 (match_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 4 (trade_price record) ++
      encode_bytes 7 (participant_id_owner record) ++
      encode_bytes 7 (participant_id_counterparty record) ++
      encode_bytes 1 (printable record) ++
      encode_bytes 1 (occurred_at_cross record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (match_id_value, bytes) =>
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
                              | Some (participant_id_owner_value, bytes) =>
                                  match decode_bytes 7 bytes with
                                  | None => None
                                  | Some (participant_id_counterparty_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (printable_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (occurred_at_cross_value, bytes) =>
                                              Some ({| nanoseconds := nanoseconds_value; match_id := match_id_value; side := side_value; quantity := quantity_value; order_book_id := order_book_id_value; trade_price := trade_price_value; participant_id_owner := participant_id_owner_value; participant_id_counterparty := participant_id_counterparty_value; printable := printable_value; occurred_at_cross := occurred_at_cross_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module EquilibriumPriceUpdate.

    (** Used when auctions occur. The message provides the changes in equilibrium price. If any Price field has bit 31 set (the highest bit, MIN_INT) while all other bits are zero (decimal -2147483648), this means that no price is available *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      available_bid_quantity_at_equilibrium_price : N;
      available_ask_quantity_at_equilibrium_price : N;
      equilibrium_price : N;
      reserved_4_a : N;
      reserved_4_b : N;
      reserved_8_a : N;
      reserved_8_b : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (available_bid_quantity_at_equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (available_ask_quantity_at_equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (equilibrium_price record < 256 ^ N.of_nat 4)%N /\
      (reserved_4_a record < 256 ^ N.of_nat 4)%N /\
      (reserved_4_b record < 256 ^ N.of_nat 4)%N /\
      (reserved_8_a record < 256 ^ N.of_nat 8)%N /\
      (reserved_8_b record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 8 (available_bid_quantity_at_equilibrium_price record) ++
      encode_uint 8 (available_ask_quantity_at_equilibrium_price record) ++
      encode_uint 4 (equilibrium_price record) ++
      encode_uint 4 (reserved_4_a record) ++
      encode_uint 4 (reserved_4_b record) ++
      encode_uint 8 (reserved_8_a record) ++
      encode_uint 8 (reserved_8_b record).

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
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (reserved_4_a_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (reserved_4_b_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (reserved_8_a_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (reserved_8_b_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; available_bid_quantity_at_equilibrium_price := available_bid_quantity_at_equilibrium_price_value; available_ask_quantity_at_equilibrium_price := available_ask_quantity_at_equilibrium_price_value; equilibrium_price := equilibrium_price_value; reserved_4_a := reserved_4_a_value; reserved_4_b := reserved_4_b_value; reserved_8_a := reserved_8_a_value; reserved_8_b := reserved_8_b_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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

  End EquilibriumPriceUpdate.

  Module QuoteRequestMessage.

    (** Used to publish Quote Requests from clients *)
    Record t := {
      nanoseconds : N;
      order_book_id : N;
      reserved_7 : N;
      reserved_5 : N;
      reserved_1 : N;
      side : list byte;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (order_book_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_7 record < 256 ^ N.of_nat 7)%N /\
      (reserved_5 record < 256 ^ N.of_nat 5)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (order_book_id record) ++
      encode_uint 7 (reserved_7 record) ++
      encode_uint 5 (reserved_5 record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_book_id_value, bytes) =>
              match decode_uint 7 bytes with
              | None => None
              | Some (reserved_7_value, bytes) =>
                  match decode_uint 5 bytes with
                  | None => None
                  | Some (reserved_5_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  Some ({| nanoseconds := nanoseconds_value; order_book_id := order_book_id_value; reserved_7 := reserved_7_value; reserved_5 := reserved_5_value; reserved_1 := reserved_1_value; side := side_value; quantity := quantity_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRequestMessage.

End NordicDerivativesDepthOfBookV2224.
