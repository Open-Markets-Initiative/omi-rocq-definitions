From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Australian Securities Exchange New Trading Platform

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

Module AsxDerivativesNtpV105.

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

    (** A ‘seconds’ Nanoseconds is issued every second and any message thereafter will be stamped with the number of nanoseconds past the last Time message received as a time reference point *)
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

  Module EndOfBusinessTradeDateMessage.

    (** This message will be sent as the last message for a Business Trade Date to signal no further messages will be disseminated for that date. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; event_code := event_code_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End EndOfBusinessTradeDateMessage.

  Module FutureSymbolDirectoryMessage.

    (** The Future Symbol Directory message describes futures contract *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      symbol_name : list byte;
      long_name : list byte;
      isin : list byte;
      exchange : list byte;
      instrument : list byte;
      cfi_code : list byte;
      expiry_year : N;
      expiry_month : N;
      price_display_decimals : N;
      price_fractional_denominator : N;
      price_minimum_tick : N;
      last_trading_date : N;
      prior_day_settlement : N;
      currency : list byte;
      lot_size_or_face_value : N;
      maturity_value : N;
      coupon_rate : N;
      payments_per_year : N;
      block_lot_size : N;
      expiry_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_name record) = 32 /\
      Datatypes.length (long_name record) = 60 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (exchange record) = 6 /\
      Datatypes.length (instrument record) = 6 /\
      Datatypes.length (cfi_code record) = 6 /\
      (expiry_year record < 256 ^ N.of_nat 2)%N /\
      (expiry_month record < 256 ^ N.of_nat 1)%N /\
      (price_display_decimals record < 256 ^ N.of_nat 1)%N /\
      (price_fractional_denominator record < 256 ^ N.of_nat 4)%N /\
      (price_minimum_tick record < 256 ^ N.of_nat 4)%N /\
      (last_trading_date record < 256 ^ N.of_nat 4)%N /\
      (prior_day_settlement record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (currency record) = 3 /\
      (lot_size_or_face_value record < 256 ^ N.of_nat 8)%N /\
      (maturity_value record < 256 ^ N.of_nat 1)%N /\
      (coupon_rate record < 256 ^ N.of_nat 2)%N /\
      (payments_per_year record < 256 ^ N.of_nat 1)%N /\
      (block_lot_size record < 256 ^ N.of_nat 4)%N /\
      (expiry_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 32 (symbol_name record) ++
      encode_bytes 60 (long_name record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (exchange record) ++
      encode_bytes 6 (instrument record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_uint 2 (expiry_year record) ++
      encode_uint 1 (expiry_month record) ++
      encode_uint 1 (price_display_decimals record) ++
      encode_uint 4 (price_fractional_denominator record) ++
      encode_uint 4 (price_minimum_tick record) ++
      encode_uint 4 (last_trading_date record) ++
      encode_uint 8 (prior_day_settlement record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 8 (lot_size_or_face_value record) ++
      encode_uint 1 (maturity_value record) ++
      encode_uint 2 (coupon_rate record) ++
      encode_uint 1 (payments_per_year record) ++
      encode_uint 4 (block_lot_size record) ++
      encode_uint 4 (expiry_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (symbol_name_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (long_name_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (isin_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (exchange_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (instrument_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (cfi_code_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (expiry_year_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (expiry_month_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (price_display_decimals_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (price_fractional_denominator_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (price_minimum_tick_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (last_trading_date_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (prior_day_settlement_value, bytes) =>
                                                                      match decode_bytes 3 bytes with
                                                                      | None => None
                                                                      | Some (currency_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (lot_size_or_face_value_value, bytes) =>
                                                                              match decode_uint 1 bytes with
                                                                              | None => None
                                                                              | Some (maturity_value_value, bytes) =>
                                                                                  match decode_uint 2 bytes with
                                                                                  | None => None
                                                                                  | Some (coupon_rate_value, bytes) =>
                                                                                      match decode_uint 1 bytes with
                                                                                      | None => None
                                                                                      | Some (payments_per_year_value, bytes) =>
                                                                                          match decode_uint 4 bytes with
                                                                                          | None => None
                                                                                          | Some (block_lot_size_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (expiry_date_value, bytes) =>
                                                                                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; symbol_name := symbol_name_value; long_name := long_name_value; isin := isin_value; exchange := exchange_value; instrument := instrument_value; cfi_code := cfi_code_value; expiry_year := expiry_year_value; expiry_month := expiry_month_value; price_display_decimals := price_display_decimals_value; price_fractional_denominator := price_fractional_denominator_value; price_minimum_tick := price_minimum_tick_value; last_trading_date := last_trading_date_value; prior_day_settlement := prior_day_settlement_value; currency := currency_value; lot_size_or_face_value := lot_size_or_face_value_value; maturity_value := maturity_value_value; coupon_rate := coupon_rate_value; payments_per_year := payments_per_year_value; block_lot_size := block_lot_size_value; expiry_date := expiry_date_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 179.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 bound_22]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FutureSymbolDirectoryMessage.

  Module OptionsSymbolDirectoryMessage.

    (** The Options Symbol Directory message describes options and warrants contracts. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      symbol_name : list byte;
      long_name : list byte;
      isin : list byte;
      exchange : list byte;
      instrument : list byte;
      cfi_code : list byte;
      expiry_year : N;
      expiry_month : N;
      option_type : list byte;
      strike : N;
      underlying_tradeable_instrument_id : N;
      price_display_decimals : N;
      price_fractional_denominator : N;
      price_minimum_tick : N;
      strike_price_decimal_position : N;
      strike_price_fractional_denominator : N;
      strike_price_minimum_tick : N;
      last_trading_date : N;
      prior_day_settlement : N;
      volatility : N;
      currency : list byte;
      lot_size_or_face_value : N;
      maturity_value : N;
      coupon_rate : N;
      payments_per_year : N;
      block_lot_size : N;
      expiry_date : N;
      basis_of_quotation : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol_name record) = 32 /\
      Datatypes.length (long_name record) = 60 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (exchange record) = 6 /\
      Datatypes.length (instrument record) = 6 /\
      Datatypes.length (cfi_code record) = 6 /\
      (expiry_year record < 256 ^ N.of_nat 2)%N /\
      (expiry_month record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (option_type record) = 1 /\
      (strike record < 256 ^ N.of_nat 8)%N /\
      (underlying_tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (price_display_decimals record < 256 ^ N.of_nat 1)%N /\
      (price_fractional_denominator record < 256 ^ N.of_nat 4)%N /\
      (price_minimum_tick record < 256 ^ N.of_nat 4)%N /\
      (strike_price_decimal_position record < 256 ^ N.of_nat 1)%N /\
      (strike_price_fractional_denominator record < 256 ^ N.of_nat 4)%N /\
      (strike_price_minimum_tick record < 256 ^ N.of_nat 4)%N /\
      (last_trading_date record < 256 ^ N.of_nat 4)%N /\
      (prior_day_settlement record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (currency record) = 3 /\
      (lot_size_or_face_value record < 256 ^ N.of_nat 8)%N /\
      (maturity_value record < 256 ^ N.of_nat 1)%N /\
      (coupon_rate record < 256 ^ N.of_nat 2)%N /\
      (payments_per_year record < 256 ^ N.of_nat 1)%N /\
      (block_lot_size record < 256 ^ N.of_nat 4)%N /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (basis_of_quotation record) = 10.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 32 (symbol_name record) ++
      encode_bytes 60 (long_name record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (exchange record) ++
      encode_bytes 6 (instrument record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_uint 2 (expiry_year record) ++
      encode_uint 1 (expiry_month record) ++
      encode_bytes 1 (option_type record) ++
      encode_uint 8 (strike record) ++
      encode_uint 4 (underlying_tradeable_instrument_id record) ++
      encode_uint 1 (price_display_decimals record) ++
      encode_uint 4 (price_fractional_denominator record) ++
      encode_uint 4 (price_minimum_tick record) ++
      encode_uint 1 (strike_price_decimal_position record) ++
      encode_uint 4 (strike_price_fractional_denominator record) ++
      encode_uint 4 (strike_price_minimum_tick record) ++
      encode_uint 4 (last_trading_date record) ++
      encode_uint 8 (prior_day_settlement record) ++
      encode_uint 8 (volatility record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 8 (lot_size_or_face_value record) ++
      encode_uint 1 (maturity_value record) ++
      encode_uint 2 (coupon_rate record) ++
      encode_uint 1 (payments_per_year record) ++
      encode_uint 4 (block_lot_size record) ++
      encode_uint 4 (expiry_date record) ++
      encode_bytes 10 (basis_of_quotation record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 32 bytes with
                  | None => None
                  | Some (symbol_name_value, bytes) =>
                      match decode_bytes 60 bytes with
                      | None => None
                      | Some (long_name_value, bytes) =>
                          match decode_bytes 12 bytes with
                          | None => None
                          | Some (isin_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (exchange_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (instrument_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (cfi_code_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (expiry_year_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (expiry_month_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (option_type_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (strike_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (underlying_tradeable_instrument_id_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (price_display_decimals_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (price_fractional_denominator_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (price_minimum_tick_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (strike_price_decimal_position_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (strike_price_fractional_denominator_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (strike_price_minimum_tick_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (last_trading_date_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (prior_day_settlement_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (volatility_value, bytes) =>
                                                                                                  match decode_bytes 3 bytes with
                                                                                                  | None => None
                                                                                                  | Some (currency_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (lot_size_or_face_value_value, bytes) =>
                                                                                                          match decode_uint 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (maturity_value_value, bytes) =>
                                                                                                              match decode_uint 2 bytes with
                                                                                                              | None => None
                                                                                                              | Some (coupon_rate_value, bytes) =>
                                                                                                                  match decode_uint 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (payments_per_year_value, bytes) =>
                                                                                                                      match decode_uint 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (block_lot_size_value, bytes) =>
                                                                                                                          match decode_uint 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (expiry_date_value, bytes) =>
                                                                                                                              match decode_bytes 10 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (basis_of_quotation_value, bytes) =>
                                                                                                                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; symbol_name := symbol_name_value; long_name := long_name_value; isin := isin_value; exchange := exchange_value; instrument := instrument_value; cfi_code := cfi_code_value; expiry_year := expiry_year_value; expiry_month := expiry_month_value; option_type := option_type_value; strike := strike_value; underlying_tradeable_instrument_id := underlying_tradeable_instrument_id_value; price_display_decimals := price_display_decimals_value; price_fractional_denominator := price_fractional_denominator_value; price_minimum_tick := price_minimum_tick_value; strike_price_decimal_position := strike_price_decimal_position_value; strike_price_fractional_denominator := strike_price_fractional_denominator_value; strike_price_minimum_tick := strike_price_minimum_tick_value; last_trading_date := last_trading_date_value; prior_day_settlement := prior_day_settlement_value; volatility := volatility_value; currency := currency_value; lot_size_or_face_value := lot_size_or_face_value_value; maturity_value := maturity_value_value; coupon_rate := coupon_rate_value; payments_per_year := payments_per_year_value; block_lot_size := block_lot_size_value; expiry_date := expiry_date_value; basis_of_quotation := basis_of_quotation_value |}, bytes)
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
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 219.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 bound_30]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
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
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsSymbolDirectoryMessage.

  Module OrderBookStateMessage.

    (** This message indicates the current session state of a contract to the market *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      session_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (session_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (session_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (session_state_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; session_state := session_state_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End OrderBookStateMessage.

  Module AddOrderMessage.

    (** An Order Added message indicates a new order or a restated order that has been accepted by the matching engine and added to the order book *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
      order_book_priority : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_priority record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (order_book_priority record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_book_priority_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value; order_book_priority := order_book_priority_value; quantity := quantity_value; price := price_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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

  End AddOrderMessage.

  Module OrderVolumeCancelledMessage.

    (** An Order Volume Cancelled message is sent when an order is modified as a result of partial cancellation of volume *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value; quantity := quantity_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderVolumeCancelledMessage.

  Module OrderDeletedMessage.

    (** This message is sent whenever an order in the book is cancelled by the owner, expired, cancelled by the exchange, purged or volume cancelled *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value |}, bytes)
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

  End OrderDeletedMessage.

  Module OrderExecutedMessage.

    (** This message is sent whenever a resting order of the book is executed in whole or in part and the counterparty to the trade is an aggressive order *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
      quantity_remaining : N;
      trade_type : list byte;
      trade_id : N;
      executed_quantity : N;
      trade_price : N;
      combination_trade_id : N;
      counter_party_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (combination_trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (counter_party_id record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (combination_trade_id record) ++
      encode_bytes 3 (counter_party_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_remaining_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (executed_quantity_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trade_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (combination_trade_id_value, bytes) =>
                                                  match decode_bytes 3 bytes with
                                                  | None => None
                                                  | Some (counter_party_id_value, bytes) =>
                                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value; quantity_remaining := quantity_remaining_value; trade_type := trade_type_value; trade_id := trade_id_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; combination_trade_id := combination_trade_id_value; counter_party_id := counter_party_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 55.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module AuctionOrderExecutedMessage.

    (** This message is sent when orders are executed in the auction at the open of the market *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
      quantity_remaining : N;
      trade_type : list byte;
      trade_id : N;
      executed_quantity : N;
      trade_price : N;
      opposite_order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (opposite_order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (opposite_order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_remaining_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (executed_quantity_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trade_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (opposite_order_id_value, bytes) =>
                                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value; quantity_remaining := quantity_remaining_value; trade_type := trade_type_value; trade_id := trade_id_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; opposite_order_id := opposite_order_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionOrderExecutedMessage.

  Module CombinationOrderExecutedMessage.

    (** This message is sent whenever a resting order is matched with an open leg of a resting combination order in whole or in part *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
      quantity_remaining : N;
      trade_type : list byte;
      trade_id : N;
      executed_quantity : N;
      trade_price : N;
      opposite_tradeable_instrument_id : N;
      opposite_side : list byte;
      opposite_order_id : N;
      combination_trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (opposite_tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (opposite_side record) = 1 /\
      (opposite_order_id record < 256 ^ N.of_nat 8)%N /\
      (combination_trade_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 4 (quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (opposite_tradeable_instrument_id record) ++
      encode_bytes 1 (opposite_side record) ++
      encode_uint 8 (opposite_order_id record) ++
      encode_uint 8 (combination_trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_remaining_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (trade_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (executed_quantity_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (trade_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (opposite_tradeable_instrument_id_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (opposite_side_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (opposite_order_id_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (combination_trade_id_value, bytes) =>
                                                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value; quantity_remaining := quantity_remaining_value; trade_type := trade_type_value; trade_id := trade_id_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; opposite_tradeable_instrument_id := opposite_tradeable_instrument_id_value; opposite_side := opposite_side_value; opposite_order_id := opposite_order_id_value; combination_trade_id := combination_trade_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 65.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CombinationOrderExecutedMessage.

  Module ImpliedOrderAddedMessage.

    (** This message is a similar format to the Order Added message, except the nature of this order is it has an implied price, implied volume and a priority that is derived from two or more “real” orders deriving the implied price *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
      order_book_priority : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_priority record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (order_book_priority record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_book_priority_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value; order_book_priority := order_book_priority_value; quantity := quantity_value; price := price_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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

  End ImpliedOrderAddedMessage.

  Module ImpliedOrderReplacedMessage.

    (** This message notifies the subscriber that an existing implied order is to be replaced when the implied price, volume or priority has changed due to a price or volume movement of “real” orders for a side of a single Tradeable Instrument Id *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
      order_book_priority : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (order_book_priority record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 8 (order_book_priority record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_book_priority_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value; order_book_priority := order_book_priority_value; quantity := quantity_value; price := price_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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

  End ImpliedOrderReplacedMessage.

  Module ImpliedOrderDeletedMessage.

    (** This message is sent whenever the implied pricing or volume has changed due to price or volume movement of “real” orders for a side of a single contract number. When received, any implied volume is no longer accessible so the “implied” order of the indicated side must be removed from the book *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      side : list byte;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; side := side_value; order_id := order_id_value |}, bytes)
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

  End ImpliedOrderDeletedMessage.

  Module TradeExecutedMessage.

    (** The Trade Message is designed to provide details for executions in combination order books. Trade Executed messages are reported in the same sequence as order execution messages are reported *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      trade_type : list byte;
      trade_id : N;
      executed_quantity : N;
      trade_price : N;
      combination_trade_id : N;
      participant_id_buyer : list byte;
      participant_id_seller : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (combination_trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (participant_id_buyer record) = 3 /\
      Datatypes.length (participant_id_seller record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 8 (combination_trade_id record) ++
      encode_bytes 3 (participant_id_buyer record) ++
      encode_bytes 3 (participant_id_seller record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trade_type_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (executed_quantity_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (combination_trade_id_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (participant_id_buyer_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (participant_id_seller_value, bytes) =>
                                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; trade_type := trade_type_value; trade_id := trade_id_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; combination_trade_id := combination_trade_id_value; participant_id_buyer := participant_id_buyer_value; participant_id_seller := participant_id_seller_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 45.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeExecutedMessage.

  Module CombinationTradeExecutedMessage.

    (** The Combination Trade Executed Message is designed to provide details for executions where one or both orders are resting from a different order book id from the order book id of the trade *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      trade_type : list byte;
      trade_id : N;
      executed_quantity : N;
      trade_price : N;
      buyer_tradeable_instrument_id : N;
      buyer_side : list byte;
      buyer_order_id : N;
      buyer_combination_trade_id : N;
      buyer_participant_id : list byte;
      seller_tradeable_instrument_id : N;
      seller_side : list byte;
      seller_order_id : N;
      seller_combination_trade_id : N;
      seller_participant_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (buyer_tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (buyer_side record) = 1 /\
      (buyer_order_id record < 256 ^ N.of_nat 8)%N /\
      (buyer_combination_trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buyer_participant_id record) = 3 /\
      (seller_tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (seller_side record) = 1 /\
      (seller_order_id record < 256 ^ N.of_nat 8)%N /\
      (seller_combination_trade_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (seller_participant_id record) = 3.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (buyer_tradeable_instrument_id record) ++
      encode_bytes 1 (buyer_side record) ++
      encode_uint 8 (buyer_order_id record) ++
      encode_uint 8 (buyer_combination_trade_id record) ++
      encode_bytes 3 (buyer_participant_id record) ++
      encode_uint 4 (seller_tradeable_instrument_id record) ++
      encode_bytes 1 (seller_side record) ++
      encode_uint 8 (seller_order_id record) ++
      encode_uint 8 (seller_combination_trade_id record) ++
      encode_bytes 3 (seller_participant_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trade_type_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (executed_quantity_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (buyer_tradeable_instrument_id_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (buyer_side_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (buyer_order_id_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (buyer_combination_trade_id_value, bytes) =>
                                                  match decode_bytes 3 bytes with
                                                  | None => None
                                                  | Some (buyer_participant_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (seller_tradeable_instrument_id_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (seller_side_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (seller_order_id_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (seller_combination_trade_id_value, bytes) =>
                                                                      match decode_bytes 3 bytes with
                                                                      | None => None
                                                                      | Some (seller_participant_id_value, bytes) =>
                                                                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; trade_type := trade_type_value; trade_id := trade_id_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; buyer_tradeable_instrument_id := buyer_tradeable_instrument_id_value; buyer_side := buyer_side_value; buyer_order_id := buyer_order_id_value; buyer_combination_trade_id := buyer_combination_trade_id_value; buyer_participant_id := buyer_participant_id_value; seller_tradeable_instrument_id := seller_tradeable_instrument_id_value; seller_side := seller_side_value; seller_order_id := seller_order_id_value; seller_combination_trade_id := seller_combination_trade_id_value; seller_participant_id := seller_participant_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 79.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CombinationTradeExecutedMessage.

  Module TradeCancellationMessage.

    (** This message is sent whenever a trade is cancelled by ASX *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_uint 8 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; trade_id := trade_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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

  End TradeCancellationMessage.

  Module EquilibriumPriceMessage.

    (** This message is disseminated in response to changes in the equilibrium price for an order book during a pre-open period *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      equilibrium_price : N;
      matched_quantity : N;
      bid_quantity : N;
      ask_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (equilibrium_price record < 256 ^ N.of_nat 8)%N /\
      (matched_quantity record < 256 ^ N.of_nat 8)%N /\
      (bid_quantity record < 256 ^ N.of_nat 8)%N /\
      (ask_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_uint 8 (equilibrium_price record) ++
      encode_uint 8 (matched_quantity record) ++
      encode_uint 8 (bid_quantity record) ++
      encode_uint 8 (ask_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (equilibrium_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (matched_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_quantity_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (ask_quantity_value, bytes) =>
                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; equilibrium_price := equilibrium_price_value; matched_quantity := matched_quantity_value; bid_quantity := bid_quantity_value; ask_quantity := ask_quantity_value |}, bytes)
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

  End EquilibriumPriceMessage.

  Module OpenHighLowLastTradeAdjustmentMessage.

    (** Market trade price adjustments are sent resulting from modifications of Open, High, Low, Last and volume statistics due to market operations, prior to the instrument moving to the next session within the trade date, or at the close of instrument *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      opening_trade : N;
      highest_trade : N;
      lowest_trade : N;
      last_trade : N;
      last_volume : N;
      total_traded_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (opening_trade record < 256 ^ N.of_nat 8)%N /\
      (highest_trade record < 256 ^ N.of_nat 8)%N /\
      (lowest_trade record < 256 ^ N.of_nat 8)%N /\
      (last_trade record < 256 ^ N.of_nat 8)%N /\
      (last_volume record < 256 ^ N.of_nat 4)%N /\
      (total_traded_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_uint 8 (opening_trade record) ++
      encode_uint 8 (highest_trade record) ++
      encode_uint 8 (lowest_trade record) ++
      encode_uint 8 (last_trade record) ++
      encode_uint 4 (last_volume record) ++
      encode_uint 8 (total_traded_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (opening_trade_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (highest_trade_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (lowest_trade_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (last_trade_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (last_volume_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (total_traded_volume_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; opening_trade := opening_trade_value; highest_trade := highest_trade_value; lowest_trade := lowest_trade_value; last_trade := last_trade_value; last_volume := last_volume_value; total_traded_volume := total_traded_volume_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
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

  End OpenHighLowLastTradeAdjustmentMessage.

  Module MarketSettlementMessage.

    (** This message disseminates the final settlement price of a future or option contracts order book for the trade date it pertains to *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      opening_trade : N;
      highest_trade : N;
      lowest_trade : N;
      last_trade : N;
      last_volume : N;
      total_traded_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (opening_trade record < 256 ^ N.of_nat 8)%N /\
      (highest_trade record < 256 ^ N.of_nat 8)%N /\
      (lowest_trade record < 256 ^ N.of_nat 8)%N /\
      (last_trade record < 256 ^ N.of_nat 8)%N /\
      (last_volume record < 256 ^ N.of_nat 4)%N /\
      (total_traded_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_uint 8 (opening_trade record) ++
      encode_uint 8 (highest_trade record) ++
      encode_uint 8 (lowest_trade record) ++
      encode_uint 8 (last_trade record) ++
      encode_uint 4 (last_volume record) ++
      encode_uint 8 (total_traded_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (opening_trade_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (highest_trade_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (lowest_trade_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (last_trade_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (last_volume_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (total_traded_volume_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; opening_trade := opening_trade_value; highest_trade := highest_trade_value; lowest_trade := lowest_trade_value; last_trade := last_trade_value; last_volume := last_volume_value; total_traded_volume := total_traded_volume_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
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

  End MarketSettlementMessage.

  Module TextMessage.

    (** This message disseminates free text information describing ad-hoc market events *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      source_id : list byte;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (source_id record) = 6 /\
      Datatypes.length (text record) = 100.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_bytes 6 (source_id record) ++
      encode_bytes 100 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (source_id_value, bytes) =>
                  match decode_bytes 100 bytes with
                  | None => None
                  | Some (text_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; source_id := source_id_value; text := text_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TextMessage.

  Module RequestForQuoteMessage.

    (** This message is disseminated for anonymous Request for Quotes (RFQs) from the market *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      rfq_side : list byte;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (rfq_side record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_bytes 1 (rfq_side record) ++
      encode_uint 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (rfq_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; rfq_side := rfq_side_value; quantity := quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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

  End RequestForQuoteMessage.

  Module AnomalousOrderThresholdPublishMessage.

    (** This message disseminates price band information to the market advising the setting, zeroing or adjusting of the Extreme Trade Range price, the Anomalous Order Threshold price and the associated ranges for a contract that requires Market Integrity Rules enforcement *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      aot_price : N;
      aot_upper_price : N;
      aot_lower_price : N;
      etr_price : N;
      etr_upper_price : N;
      etr_lower_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (aot_price record < 256 ^ N.of_nat 8)%N /\
      (aot_upper_price record < 256 ^ N.of_nat 8)%N /\
      (aot_lower_price record < 256 ^ N.of_nat 8)%N /\
      (etr_price record < 256 ^ N.of_nat 8)%N /\
      (etr_upper_price record < 256 ^ N.of_nat 8)%N /\
      (etr_lower_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_uint 8 (aot_price record) ++
      encode_uint 8 (aot_upper_price record) ++
      encode_uint 8 (aot_lower_price record) ++
      encode_uint 8 (etr_price record) ++
      encode_uint 8 (etr_upper_price record) ++
      encode_uint 8 (etr_lower_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (aot_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (aot_upper_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (aot_lower_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (etr_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (etr_upper_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (etr_lower_price_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; aot_price := aot_price_value; aot_upper_price := aot_upper_price_value; aot_lower_price := aot_lower_price_value; etr_price := etr_price_value; etr_upper_price := etr_upper_price_value; etr_lower_price := etr_lower_price_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 58.
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

  End AnomalousOrderThresholdPublishMessage.

  Module VolumeAndOpenInterestMessage.

    (** This message disseminates Volume and Open Interest (VOI) information for each trade date *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      tradeable_instrument_id : N;
      cumulative_volume : N;
      open_interest : N;
      voi_trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (tradeable_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (cumulative_volume record < 256 ^ N.of_nat 8)%N /\
      (open_interest record < 256 ^ N.of_nat 8)%N /\
      (voi_trade_date record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (tradeable_instrument_id record) ++
      encode_uint 8 (cumulative_volume record) ++
      encode_uint 8 (open_interest record) ++
      encode_uint 2 (voi_trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tradeable_instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (cumulative_volume_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (open_interest_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (voi_trade_date_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; tradeable_instrument_id := tradeable_instrument_id_value; cumulative_volume := cumulative_volume_value; open_interest := open_interest_value; voi_trade_date := voi_trade_date_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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

  End VolumeAndOpenInterestMessage.

End AsxDerivativesNtpV105.
