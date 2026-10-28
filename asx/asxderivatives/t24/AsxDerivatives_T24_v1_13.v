From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Australian Securities Exchange 24 Itch

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

Module AsxDerivativesT24V113.

  Module Session.

    Record t := {
      protocol_version : list byte;
      session_year : list byte;
      session_week : list byte;
      trading_service : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (protocol_version record) = 3 /\
      Datatypes.length (session_year record) = 2 /\
      Datatypes.length (session_week record) = 2 /\
      Datatypes.length (trading_service record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 3 (protocol_version record) ++
      encode_bytes 2 (session_year record) ++
      encode_bytes 2 (session_week record) ++
      encode_bytes 3 (trading_service record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 3 bytes with
      | None => None
      | Some (protocol_version_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (session_year_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (session_week_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (trading_service_value, bytes) =>
                      Some ({| protocol_version := protocol_version_value; session_year := session_year_value; session_week := session_week_value; trading_service := trading_service_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End Session.

  Module PacketHeader.

    (** Itch Mold Udp 64 Packet Header *)
    Record t := {
      session : Session.t;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Session.bounded (session record) /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      Session.encode (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Session.decode bytes with
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
      rewrite !length_app, !Session.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Session.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Session.eq_dec]. Defined.

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

  Module TimeMessage.

    (** The server will, on each packet multicast, transmit this message for every second for which at least one application message is generated *)
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

  End TimeMessage.

  Module SystemEventMessage.

    (** The system event message is used to signal a market or trading period event. *)
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

  End SystemEventMessage.

  Module FutureSymbolDirectoryMessage.

    (** As each product moves to the new Trade Date, ASX Trade24 will disseminate the future symbol messages defining the available futures, CFDs and Share Future contracts for each instrument. The action of disseminating this message will automatically imply the contract is in a “Pending” session state. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      exchange : list byte;
      instrument : list byte;
      contract_type : list byte;
      expiry_year : N;
      expiry_month : N;
      price_decimal_position : N;
      price_fractional_denominator : N;
      price_minimum_tick : N;
      last_trading_date : N;
      prior_day_settlement : N;
      financial_type : list byte;
      currency : list byte;
      lot_size_or_face_value : N;
      maturity_value : N;
      coupon_rate : N;
      payments_per_year : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exchange record) = 6 /\
      Datatypes.length (instrument record) = 6 /\
      Datatypes.length (contract_type record) = 1 /\
      (expiry_year record < 256 ^ N.of_nat 2)%N /\
      (expiry_month record < 256 ^ N.of_nat 1)%N /\
      (price_decimal_position record < 256 ^ N.of_nat 1)%N /\
      (price_fractional_denominator record < 256 ^ N.of_nat 4)%N /\
      (price_minimum_tick record < 256 ^ N.of_nat 2)%N /\
      (last_trading_date record < 256 ^ N.of_nat 4)%N /\
      (prior_day_settlement record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_type record) = 1 /\
      Datatypes.length (currency record) = 3 /\
      (lot_size_or_face_value record < 256 ^ N.of_nat 4)%N /\
      (maturity_value record < 256 ^ N.of_nat 1)%N /\
      (coupon_rate record < 256 ^ N.of_nat 2)%N /\
      (payments_per_year record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 6 (exchange record) ++
      encode_bytes 6 (instrument record) ++
      encode_bytes 1 (contract_type record) ++
      encode_uint 2 (expiry_year record) ++
      encode_uint 1 (expiry_month record) ++
      encode_uint 1 (price_decimal_position record) ++
      encode_uint 4 (price_fractional_denominator record) ++
      encode_uint 2 (price_minimum_tick record) ++
      encode_uint 4 (last_trading_date record) ++
      encode_uint 4 (prior_day_settlement record) ++
      encode_bytes 1 (financial_type record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 4 (lot_size_or_face_value record) ++
      encode_uint 1 (maturity_value record) ++
      encode_uint 2 (coupon_rate record) ++
      encode_uint 1 (payments_per_year record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (exchange_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (instrument_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (contract_type_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (expiry_year_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (expiry_month_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (price_decimal_position_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (price_fractional_denominator_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (price_minimum_tick_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (last_trading_date_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (prior_day_settlement_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (financial_type_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (currency_value, bytes) =>
                                                                  match decode_uint 4 bytes with
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
                                                                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; exchange := exchange_value; instrument := instrument_value; contract_type := contract_type_value; expiry_year := expiry_year_value; expiry_month := expiry_month_value; price_decimal_position := price_decimal_position_value; price_fractional_denominator := price_fractional_denominator_value; price_minimum_tick := price_minimum_tick_value; last_trading_date := last_trading_date_value; prior_day_settlement := prior_day_settlement_value; financial_type := financial_type_value; currency := currency_value; lot_size_or_face_value := lot_size_or_face_value_value; maturity_value := maturity_value_value; coupon_rate := coupon_rate_value; payments_per_year := payments_per_year_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 53.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FutureSymbolDirectoryMessage.

  Module SpreadSymbolDirectoryMessage.

    (** As each product moves to the new Trade Date, ASX Trade24 will disseminate the spread symbol messages defining the available calendar spread and inter-spread contracts. For contracts that are inter-spreads, the underlying legs are in the same Trade Date. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      exchange : list byte;
      contract_type : list byte;
      first_leg_contract_number : N;
      second_leg_contract_number : N;
      primary_ratio : N;
      secondary_ratio : N;
      price_decimal_position : N;
      price_fractional_denominator : N;
      price_minimum_tick : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exchange record) = 6 /\
      Datatypes.length (contract_type record) = 1 /\
      (first_leg_contract_number record < 256 ^ N.of_nat 4)%N /\
      (second_leg_contract_number record < 256 ^ N.of_nat 4)%N /\
      (primary_ratio record < 256 ^ N.of_nat 1)%N /\
      (secondary_ratio record < 256 ^ N.of_nat 1)%N /\
      (price_decimal_position record < 256 ^ N.of_nat 1)%N /\
      (price_fractional_denominator record < 256 ^ N.of_nat 4)%N /\
      (price_minimum_tick record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 6 (exchange record) ++
      encode_bytes 1 (contract_type record) ++
      encode_uint 4 (first_leg_contract_number record) ++
      encode_uint 4 (second_leg_contract_number record) ++
      encode_uint 1 (primary_ratio record) ++
      encode_uint 1 (secondary_ratio record) ++
      encode_uint 1 (price_decimal_position record) ++
      encode_uint 4 (price_fractional_denominator record) ++
      encode_uint 2 (price_minimum_tick record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (exchange_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (contract_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (first_leg_contract_number_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (second_leg_contract_number_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (primary_ratio_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (secondary_ratio_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (price_decimal_position_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (price_fractional_denominator_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (price_minimum_tick_value, bytes) =>
                                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; exchange := exchange_value; contract_type := contract_type_value; first_leg_contract_number := first_leg_contract_number_value; second_leg_contract_number := second_leg_contract_number_value; primary_ratio := primary_ratio_value; secondary_ratio := secondary_ratio_value; price_decimal_position := price_decimal_position_value; price_fractional_denominator := price_fractional_denominator_value; price_minimum_tick := price_minimum_tick_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpreadSymbolDirectoryMessage.

  Module OptionSymbolDirectoryMessage.

    (** As each product moves to the new Trade Date, ASX Trade24 will disseminate the option symbol messages defining all the available options contracts. For Single Session Options only, the exchange can activate or de-activate option symbols during the course of trading by issuing Order Book State messages for affected option contracts. If an option symbol is not active (Activated field is ‘N’) or is de-activated (Trading Status is “I”), reference to that option contract should be removed from the list of actively traded contracts. If an option symbol is active (Activated field is ‘Y’) or is activated (Trading Status is “A”), reference to that option contract should be added to the list of actively traded contracts. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      exchange : list byte;
      instrument : list byte;
      contract_type : list byte;
      expiry_year : N;
      expiry_month : N;
      option_type : list byte;
      strike : N;
      underlying_contract_number : N;
      price_decimal_position : N;
      price_fractional_denominator : N;
      price_minimum_tick : N;
      strike_price_decimal_position : N;
      strike_price_fractional_denominator : N;
      strike_price_minimum_tick : N;
      last_trading_date : N;
      prior_day_settlement : N;
      volatility : N;
      financial_type : list byte;
      currency : list byte;
      lot_size_or_face_value : N;
      maturity_value : N;
      coupon_rate : N;
      payments_per_year : N;
      activated : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (exchange record) = 6 /\
      Datatypes.length (instrument record) = 6 /\
      Datatypes.length (contract_type record) = 1 /\
      (expiry_year record < 256 ^ N.of_nat 2)%N /\
      (expiry_month record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (option_type record) = 1 /\
      (strike record < 256 ^ N.of_nat 4)%N /\
      (underlying_contract_number record < 256 ^ N.of_nat 4)%N /\
      (price_decimal_position record < 256 ^ N.of_nat 1)%N /\
      (price_fractional_denominator record < 256 ^ N.of_nat 4)%N /\
      (price_minimum_tick record < 256 ^ N.of_nat 2)%N /\
      (strike_price_decimal_position record < 256 ^ N.of_nat 1)%N /\
      (strike_price_fractional_denominator record < 256 ^ N.of_nat 4)%N /\
      (strike_price_minimum_tick record < 256 ^ N.of_nat 2)%N /\
      (last_trading_date record < 256 ^ N.of_nat 4)%N /\
      (prior_day_settlement record < 256 ^ N.of_nat 4)%N /\
      (volatility record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (financial_type record) = 1 /\
      Datatypes.length (currency record) = 3 /\
      (lot_size_or_face_value record < 256 ^ N.of_nat 4)%N /\
      (maturity_value record < 256 ^ N.of_nat 1)%N /\
      (coupon_rate record < 256 ^ N.of_nat 2)%N /\
      (payments_per_year record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (activated record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 6 (exchange record) ++
      encode_bytes 6 (instrument record) ++
      encode_bytes 1 (contract_type record) ++
      encode_uint 2 (expiry_year record) ++
      encode_uint 1 (expiry_month record) ++
      encode_bytes 1 (option_type record) ++
      encode_uint 4 (strike record) ++
      encode_uint 4 (underlying_contract_number record) ++
      encode_uint 1 (price_decimal_position record) ++
      encode_uint 4 (price_fractional_denominator record) ++
      encode_uint 2 (price_minimum_tick record) ++
      encode_uint 1 (strike_price_decimal_position record) ++
      encode_uint 4 (strike_price_fractional_denominator record) ++
      encode_uint 2 (strike_price_minimum_tick record) ++
      encode_uint 4 (last_trading_date record) ++
      encode_uint 4 (prior_day_settlement record) ++
      encode_uint 4 (volatility record) ++
      encode_bytes 1 (financial_type record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 4 (lot_size_or_face_value record) ++
      encode_uint 1 (maturity_value record) ++
      encode_uint 2 (coupon_rate record) ++
      encode_uint 1 (payments_per_year record) ++
      encode_bytes 1 (activated record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (exchange_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (instrument_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (contract_type_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (expiry_year_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (expiry_month_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (option_type_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (strike_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (underlying_contract_number_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (price_decimal_position_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (price_fractional_denominator_value, bytes) =>
                                                          match decode_uint 2 bytes with
                                                          | None => None
                                                          | Some (price_minimum_tick_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (strike_price_decimal_position_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (strike_price_fractional_denominator_value, bytes) =>
                                                                      match decode_uint 2 bytes with
                                                                      | None => None
                                                                      | Some (strike_price_minimum_tick_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (last_trading_date_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (prior_day_settlement_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (volatility_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (financial_type_value, bytes) =>
                                                                                          match decode_bytes 3 bytes with
                                                                                          | None => None
                                                                                          | Some (currency_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
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
                                                                                                              match decode_bytes 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (activated_value, bytes) =>
                                                                                                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; exchange := exchange_value; instrument := instrument_value; contract_type := contract_type_value; expiry_year := expiry_year_value; expiry_month := expiry_month_value; option_type := option_type_value; strike := strike_value; underlying_contract_number := underlying_contract_number_value; price_decimal_position := price_decimal_position_value; price_fractional_denominator := price_fractional_denominator_value; price_minimum_tick := price_minimum_tick_value; strike_price_decimal_position := strike_price_decimal_position_value; strike_price_fractional_denominator := strike_price_fractional_denominator_value; strike_price_minimum_tick := strike_price_minimum_tick_value; last_trading_date := last_trading_date_value; prior_day_settlement := prior_day_settlement_value; volatility := volatility_value; financial_type := financial_type_value; currency := currency_value; lot_size_or_face_value := lot_size_or_face_value_value; maturity_value := maturity_value_value; coupon_rate := coupon_rate_value; payments_per_year := payments_per_year_value; activated := activated_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 bound_26]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
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
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionSymbolDirectoryMessage.

  Module OrderBookStateMessage.

    (** ASX Trade24 uses this message to indicate the current session state of a contract to the market. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      trading_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (trading_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; trading_status := trading_status_value |}, bytes)
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

  Module OrderAddedMessage.

    (** An Order Added message indicates a new order has been accepted by the ASX Trade24 system and was added to the order book. All orders in ASX Trade24 are anonymous and one “Add” type is supported for “real” orders that are not custom market orders. The message is referenced by an Order Number assigned by ASX Trade24 and is unique for the life of the order. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
      order_book_priority : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (order_book_priority record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (order_book_priority record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_priority_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value; order_book_priority := order_book_priority_value; quantity := quantity_value; price := price_value |}, bytes)
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

  End OrderAddedMessage.

  Module OrderReplacedMessage.

    (** This message is sent whenever an order in the book has been modified for price or volume where the priority changes. Even though the side and contract number cannot be changed, these fields are included in the message to provide fast look-up. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
      order_book_priority : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (order_book_priority record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (order_book_priority record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_priority_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value; order_book_priority := order_book_priority_value; quantity := quantity_value; price := price_value |}, bytes)
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

  End OrderReplacedMessage.

  Module OrderVolumeCancelledMessage.

    (** This message is sent whenever an order in the book is modified as a result of a partial cancellation of volume. The difference between this message and the Order Replaced is an Order Replaced will always show a change of order book priority in regards to the order’s position in the queue. An Order Volume Cancelled message is not sent when an order has partially traded. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record) ++
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
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value; quantity := quantity_value |}, bytes)
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

    (** This message is sent whenever an order in the book is cancelled by the owner, expired, cancelled by the exchange, purged or volume cancelled. All remaining volume is no longer accessible so the order must be removed from the book. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value |}, bytes)
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

  Module ImpliedOrderAddedMessage.

    (** This message is the same format as the Order Added message, except the nature of this order is it has an implied price, implied volume and a priority that is derived from two or more spreadable “real” orders. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
      order_book_priority : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (order_book_priority record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (order_book_priority record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_priority_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value; order_book_priority := order_book_priority_value; quantity := quantity_value; price := price_value |}, bytes)
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

    (** This message is the same format as the Order Replaced message, except this replacement refers to an implied order and is sent whenever the implied pricing or volume has changed due to a price or volume movement of “real” orders for a side of a single contract number. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
      order_book_priority : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (order_book_priority record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (order_book_priority record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (order_book_priority_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value; order_book_priority := order_book_priority_value; quantity := quantity_value; price := price_value |}, bytes)
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

    (** This message is the same format as the Order Deleted message, except this deletion refers to an implied order. When received, any implied volume is no longer accessible so the “implied” order of the indicated side must be removed from the book. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value |}, bytes)
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

  Module CustomMarketOrderReplacedMessage.

    (** This message is sent whenever an order in the custom market book has been modified for volume. Custom market order modification messages always include the Order Number of the Custom Market Order Added to which the update applies. To determine the current display volume for an order, subscribers must replace the original volume stated in the Custom Market Order Added message with the quantity stated in the Custom Market Order Replaced message of the same order number. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      order_number : N;
      order_book_priority : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (order_book_priority record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (order_book_priority record) ++
      encode_uint 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (order_book_priority_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; order_number := order_number_value; order_book_priority := order_book_priority_value; quantity := quantity_value |}, bytes)
                      end
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

  End CustomMarketOrderReplacedMessage.

  Module CustomMarketOrderDeletedMessage.

    (** This message is sent whenever an order in the custom market book is cancelled by the owner, expired, cancelled by the exchange or purged. All remaining volume is no longer accessible so the order must be removed from the book. A Custom Market Order Deleted message is not sent when an order has traded out. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      order_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 8 (order_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_number_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; order_number := order_number_value |}, bytes)
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

  End CustomMarketOrderDeletedMessage.

  Module OrderExecutedMessage.

    (** This message is sent whenever a resting order of the book is executed in whole or in part where the price and contract number of the order and trade are the same. It is possible to receive several Order Executed messages for the same order reference number if that order is executed in several parts. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
      quantity_remaining : N;
      trade_type : list byte;
      match_number : N;
      executed_quantity : N;
      trade_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (trade_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_remaining_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (match_number_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (executed_quantity_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_price_value, bytes) =>
                                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value; quantity_remaining := quantity_remaining_value; trade_type := trade_type_value; match_number := match_number_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** This message is sent whenever two resting orders of the same contract are executed. This can occur in two circumstances: During levelling in whole or in part at a price that could be different from one or both resting order prices. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      buying_order_number : N;
      buyer_quantity_remaining : N;
      selling_order_number : N;
      seller_quantity_remaining : N;
      trade_type : list byte;
      match_number : N;
      executed_quantity : N;
      trade_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      (buying_order_number record < 256 ^ N.of_nat 8)%N /\
      (buyer_quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      (selling_order_number record < 256 ^ N.of_nat 8)%N /\
      (seller_quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_uint 8 (buying_order_number record) ++
      encode_uint 4 (buyer_quantity_remaining record) ++
      encode_uint 8 (selling_order_number record) ++
      encode_uint 4 (seller_quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (trade_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (buying_order_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (buyer_quantity_remaining_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (selling_order_number_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (seller_quantity_remaining_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trade_type_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (match_number_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (executed_quantity_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (trade_price_value, bytes) =>
                                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; buying_order_number := buying_order_number_value; buyer_quantity_remaining := buyer_quantity_remaining_value; selling_order_number := selling_order_number_value; seller_quantity_remaining := seller_quantity_remaining_value; trade_type := trade_type_value; match_number := match_number_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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

  End OrderExecutedWithPriceMessage.

  Module SpreadExecutedMessage.

    (** This message is sent whenever the open leg of a resting spread order is traded in whole or in part where the price and the contract number will be different than the traded contract number. It is possible to receive several Spread Executed messages for the same order number if that order is executed in several parts. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
      quantity_remaining : N;
      trade_type : list byte;
      match_number : N;
      executed_quantity : N;
      trade_price : N;
      traded_contract_number : N;
      spread_trade_price : N;
      trade_side_of_leg : list byte;
      printable : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (traded_contract_number record < 256 ^ N.of_nat 4)%N /\
      (spread_trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_side_of_leg record) = 1 /\
      Datatypes.length (printable record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (traded_contract_number record) ++
      encode_uint 4 (spread_trade_price record) ++
      encode_bytes 1 (trade_side_of_leg record) ++
      encode_bytes 1 (printable record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_remaining_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (match_number_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (executed_quantity_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (trade_price_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (traded_contract_number_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (spread_trade_price_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_side_of_leg_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (printable_value, bytes) =>
                                                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value; quantity_remaining := quantity_remaining_value; trade_type := trade_type_value; match_number := match_number_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; traded_contract_number := traded_contract_number_value; spread_trade_price := spread_trade_price_value; trade_side_of_leg := trade_side_of_leg_value; printable := printable_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 46.
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
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpreadExecutedMessage.

  Module TradeSpreadExecutionChainMessage.

    (** This message is sent whenever two resting orders of different contracts are executed in whole or in part at a price different from the initial display price(s) such as sweeping or spreading orders. Since the execution price is different than the display price of the original Add Order, a trade price field is included within the execution message. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      buyer : N;
      side_of_buyer : list byte;
      buyer_order_number : N;
      buyer_quantity_remaining : N;
      seller_contract_number : N;
      side_of_seller : list byte;
      selling_order_number : N;
      seller_quantity_remaining : N;
      trade_type : list byte;
      match_number : N;
      executed_quantity : N;
      trade_price : N;
      traded_contract_number : N;
      spread_trade_price : N;
      printable : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (buyer record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side_of_buyer record) = 1 /\
      (buyer_order_number record < 256 ^ N.of_nat 8)%N /\
      (buyer_quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      (seller_contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side_of_seller record) = 1 /\
      (selling_order_number record < 256 ^ N.of_nat 8)%N /\
      (seller_quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (traded_contract_number record < 256 ^ N.of_nat 4)%N /\
      (spread_trade_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (printable record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (buyer record) ++
      encode_bytes 1 (side_of_buyer record) ++
      encode_uint 8 (buyer_order_number record) ++
      encode_uint 4 (buyer_quantity_remaining record) ++
      encode_uint 4 (seller_contract_number record) ++
      encode_bytes 1 (side_of_seller record) ++
      encode_uint 8 (selling_order_number record) ++
      encode_uint 4 (seller_quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (traded_contract_number record) ++
      encode_uint 4 (spread_trade_price record) ++
      encode_bytes 1 (printable record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (buyer_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_of_buyer_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (buyer_order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (buyer_quantity_remaining_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (seller_contract_number_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (side_of_seller_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (selling_order_number_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (seller_quantity_remaining_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (trade_type_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (match_number_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (executed_quantity_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (trade_price_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (traded_contract_number_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (spread_trade_price_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (printable_value, bytes) =>
                                                                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; buyer := buyer_value; side_of_buyer := side_of_buyer_value; buyer_order_number := buyer_order_number_value; buyer_quantity_remaining := buyer_quantity_remaining_value; seller_contract_number := seller_contract_number_value; side_of_seller := side_of_seller_value; selling_order_number := selling_order_number_value; seller_quantity_remaining := seller_quantity_remaining_value; trade_type := trade_type_value; match_number := match_number_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; traded_contract_number := traded_contract_number_value; spread_trade_price := spread_trade_price_value; printable := printable_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
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
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeSpreadExecutionChainMessage.

  Module CustomMarketExecutedMessage.

    (** This message is sent whenever the open leg of a resting custom market order is traded in whole or in part. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      order_number : N;
      quantity_remaining : N;
      trade_type : list byte;
      match_number : N;
      executed_quantity : N;
      trade_price : N;
      traded_contract_number : N;
      trade_side_of_leg : list byte;
      printable : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (traded_contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_side_of_leg record) = 1 /\
      Datatypes.length (printable record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (traded_contract_number record) ++
      encode_bytes 1 (trade_side_of_leg record) ++
      encode_bytes 1 (printable record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_remaining_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (trade_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (executed_quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (trade_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (traded_contract_number_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_side_of_leg_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (printable_value, bytes) =>
                                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; order_number := order_number_value; quantity_remaining := quantity_remaining_value; trade_type := trade_type_value; match_number := match_number_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; traded_contract_number := traded_contract_number_value; trade_side_of_leg := trade_side_of_leg_value; printable := printable_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CustomMarketExecutedMessage.

  Module CustomMarketTradeMessage.

    (** This message is sent whenever a resting custom market order is matched with a resting non-custom market order executed in whole or in part at a price that could be different from the initial display price(s) such as spreading orders. Since the execution price could be different than the display price of the original Order Added, a trade price field is included within the execution message. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      side : list byte;
      order_number : N;
      quantity_remaining : N;
      custom_market_order_number : N;
      custom_market_quantity_remaining : N;
      trade_type : list byte;
      match_number : N;
      executed_quantity : N;
      trade_price : N;
      traded_contract_number : N;
      trade_side_of_non_custom_order : list byte;
      printable : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (side record) = 1 /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      (custom_market_order_number record < 256 ^ N.of_nat 8)%N /\
      (custom_market_quantity_remaining record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_type record) = 1 /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 4)%N /\
      (traded_contract_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_side_of_non_custom_order record) = 1 /\
      Datatypes.length (printable record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 4 (quantity_remaining record) ++
      encode_uint 8 (custom_market_order_number record) ++
      encode_uint 4 (custom_market_quantity_remaining record) ++
      encode_bytes 1 (trade_type record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_uint 4 (trade_price record) ++
      encode_uint 4 (traded_contract_number record) ++
      encode_bytes 1 (trade_side_of_non_custom_order record) ++
      encode_bytes 1 (printable record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (quantity_remaining_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (custom_market_order_number_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (custom_market_quantity_remaining_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_type_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (match_number_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (executed_quantity_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (trade_price_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (traded_contract_number_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (trade_side_of_non_custom_order_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (printable_value, bytes) =>
                                                                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; side := side_value; order_number := order_number_value; quantity_remaining := quantity_remaining_value; custom_market_order_number := custom_market_order_number_value; custom_market_quantity_remaining := custom_market_quantity_remaining_value; trade_type := trade_type_value; match_number := match_number_value; executed_quantity := executed_quantity_value; trade_price := trade_price_value; traded_contract_number := traded_contract_number_value; trade_side_of_non_custom_order := trade_side_of_non_custom_order_value; printable := printable_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 54.
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
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CustomMarketTradeMessage.

  Module TradeCancellationMessage.

    (** This message is sent whenever a trade is cancelled by exchange operations. This message does not affect any resting orders and is more for Information purposes. Adjustments to the Open, High, Low, Last will be performed as separate action using the Open, High, Low, Last Trade Adjustment message. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (match_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (match_number_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; match_number := match_number_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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

  End TradeCancellationMessage.

  Module EquilibriumPriceAuctionInfoMessage.

    (** ASX Trade24 disseminates equilibrium prices during a price discovery period. As orders are added, modified, cancelled or deleted a message will be reported informing the market the potential opening price. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      equilibrium_price : N;
      best_bid_price : N;
      best_ask_price : N;
      best_bid_quantity : N;
      best_ask_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      (equilibrium_price record < 256 ^ N.of_nat 4)%N /\
      (best_bid_price record < 256 ^ N.of_nat 4)%N /\
      (best_ask_price record < 256 ^ N.of_nat 4)%N /\
      (best_bid_quantity record < 256 ^ N.of_nat 4)%N /\
      (best_ask_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_uint 4 (equilibrium_price record) ++
      encode_uint 4 (best_bid_price record) ++
      encode_uint 4 (best_ask_price record) ++
      encode_uint 4 (best_bid_quantity record) ++
      encode_uint 4 (best_ask_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (equilibrium_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (best_bid_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (best_ask_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (best_bid_quantity_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (best_ask_quantity_value, bytes) =>
                                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; equilibrium_price := equilibrium_price_value; best_bid_price := best_bid_price_value; best_ask_price := best_ask_price_value; best_bid_quantity := best_bid_quantity_value; best_ask_quantity := best_ask_quantity_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End EquilibriumPriceAuctionInfoMessage.

  Module MarketSettlementMessage.

    (** ASX Trade24 disseminates settlement prices for all future and option contracts in two instalments, an interim and then a final. When the contract moves to the next trade date, the Future Symbol Directory or Option Symbol Directory message will reflect the final settlement price reported from the previous trade date in the prior day settlement field. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      settlement_price : N;
      volatility : N;
      settlement_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      (settlement_price record < 256 ^ N.of_nat 4)%N /\
      (volatility record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_uint 4 (settlement_price record) ++
      encode_uint 4 (volatility record) ++
      encode_bytes 1 (settlement_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (settlement_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (volatility_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (settlement_type_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; settlement_price := settlement_price_value; volatility := volatility_value; settlement_type := settlement_type_value |}, bytes)
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

  End MarketSettlementMessage.

  Module AdHocTextMessage.

    (** ASX Trade24 disseminates text messages to inform the market of ad hoc events. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      source_id : list byte;
      text_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (source_id record) = 6 /\
      Datatypes.length (text_message record) = 100.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_bytes 6 (source_id record) ++
      encode_bytes 100 (text_message record).

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
                  | Some (text_message_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; source_id := source_id_value; text_message := text_message_value |}, bytes)
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

  End AdHocTextMessage.

  Module RequestForQuoteMessage.

    (** ASX Trade24 disseminates anonymous non-custom RFQs from the market. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_uint 4 (price record) ++
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
              | Some (contract_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; price := price_value; quantity := quantity_value |}, bytes)
                      end
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

  End RequestForQuoteMessage.

  Module AnomalousOrderThresholdPublishMessage.

    (** ASX Trade24 reports this message to inform the market of setting, zeroing or adjusting the Extreme Trade Range price (ETR), the Anomalous Order Threshold price (AOT) and the associated ranges for a contract that requires Market Integrity Rules enforcement. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
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
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      (aot_price record < 256 ^ N.of_nat 4)%N /\
      (aot_upper_price record < 256 ^ N.of_nat 4)%N /\
      (aot_lower_price record < 256 ^ N.of_nat 4)%N /\
      (etr_price record < 256 ^ N.of_nat 4)%N /\
      (etr_upper_price record < 256 ^ N.of_nat 4)%N /\
      (etr_lower_price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_uint 4 (aot_price record) ++
      encode_uint 4 (aot_upper_price record) ++
      encode_uint 4 (aot_lower_price record) ++
      encode_uint 4 (etr_price record) ++
      encode_uint 4 (etr_upper_price record) ++
      encode_uint 4 (etr_lower_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (contract_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (aot_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (aot_upper_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (aot_lower_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (etr_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (etr_upper_price_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (etr_lower_price_value, bytes) =>
                                          Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; aot_price := aot_price_value; aot_upper_price := aot_upper_price_value; aot_lower_price := aot_lower_price_value; etr_price := etr_price_value; etr_upper_price := etr_upper_price_value; etr_lower_price := etr_lower_price_value |}, bytes)
                                      end
                                  end
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

    (** ASX Trade24 disseminates volume and open interest information for each trade date. The VOI Trade Date indicates the trade date to which the information applies. *)
    Record t := {
      nanoseconds : N;
      trade_date : N;
      contract_number : N;
      cumulative_volume : N;
      open_interest : N;
      voi_trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 2)%N /\
      (contract_number record < 256 ^ N.of_nat 4)%N /\
      (cumulative_volume record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 4)%N /\
      (voi_trade_date record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 2 (trade_date record) ++
      encode_uint 4 (contract_number record) ++
      encode_uint 4 (cumulative_volume record) ++
      encode_uint 4 (open_interest record) ++
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
              | Some (contract_number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cumulative_volume_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (open_interest_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (voi_trade_date_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; trade_date := trade_date_value; contract_number := contract_number_value; cumulative_volume := cumulative_volume_value; open_interest := open_interest_value; voi_trade_date := voi_trade_date_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

End AsxDerivativesT24V113.
