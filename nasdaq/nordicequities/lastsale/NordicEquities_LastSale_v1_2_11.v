From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Nordic Equity Last Sale

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

Module NordicEquitiesLastSaleV1211.

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

  Module AdjustedClosingPriceMessage.

    (** Adjusted closing price disseminated for all active symbols at the start of each trading day *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_book : N;
      adjusted_closing_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (adjusted_closing_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 8 (adjusted_closing_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (adjusted_closing_price_value, bytes) =>
                      Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_book := order_book_value; adjusted_closing_price := adjusted_closing_price_value |}, bytes)
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

  End AdjustedClosingPriceMessage.

  Module OnExchangeTradeMessage.

    (** Relays on exchange trade transactions executed or deferred to the current business day *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      order_book : N;
      execution_date : N;
      execution_time : N;
      agreement_date : N;
      agreement_time : N;
      price_on_exchange : N;
      quantity : N;
      venue_of_execution : list byte;
      transaction_identifier_code : list byte;
      mmt_trade_flags : list byte;
      trade_type : list byte;
      mpid_buyer : list byte;
      mpid_seller : list byte;
      transaction_to_be_cleared : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (order_book record < 256 ^ N.of_nat 4)%N /\
      (execution_date record < 256 ^ N.of_nat 4)%N /\
      (execution_time record < 256 ^ N.of_nat 8)%N /\
      (agreement_date record < 256 ^ N.of_nat 4)%N /\
      (agreement_time record < 256 ^ N.of_nat 8)%N /\
      (price_on_exchange record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (venue_of_execution record) = 4 /\
      Datatypes.length (transaction_identifier_code record) = 10 /\
      Datatypes.length (mmt_trade_flags record) = 14 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (mpid_buyer record) = 4 /\
      Datatypes.length (mpid_seller record) = 4 /\
      Datatypes.length (transaction_to_be_cleared record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_uint 4 (order_book record) ++
      encode_uint 4 (execution_date record) ++
      encode_uint 8 (execution_time record) ++
      encode_uint 4 (agreement_date record) ++
      encode_uint 8 (agreement_time record) ++
      encode_uint 8 (price_on_exchange record) ++
      encode_uint 8 (quantity record) ++
      encode_bytes 4 (venue_of_execution record) ++
      encode_bytes 10 (transaction_identifier_code record) ++
      encode_bytes 14 (mmt_trade_flags record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 4 (mpid_buyer record) ++
      encode_bytes 4 (mpid_seller record) ++
      encode_bytes 1 (transaction_to_be_cleared record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_book_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (execution_date_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (execution_time_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (agreement_date_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (agreement_time_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_on_exchange_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (quantity_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (venue_of_execution_value, bytes) =>
                                              match decode_bytes 10 bytes with
                                              | None => None
                                              | Some (transaction_identifier_code_value, bytes) =>
                                                  match decode_bytes 14 bytes with
                                                  | None => None
                                                  | Some (mmt_trade_flags_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_type_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (mpid_buyer_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (mpid_seller_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (transaction_to_be_cleared_value, bytes) =>
                                                                      Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; order_book := order_book_value; execution_date := execution_date_value; execution_time := execution_time_value; agreement_date := agreement_date_value; agreement_time := agreement_time_value; price_on_exchange := price_on_exchange_value; quantity := quantity_value; venue_of_execution := venue_of_execution_value; transaction_identifier_code := transaction_identifier_code_value; mmt_trade_flags := mmt_trade_flags_value; trade_type := trade_type_value; mpid_buyer := mpid_buyer_value; mpid_seller := mpid_seller_value; transaction_to_be_cleared := transaction_to_be_cleared_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OnExchangeTradeMessage.

  Module OtcTradeMessage.

    (** Relays over the counter and systematic internaliser trade transactions *)
    Record t := {
      timestamp : N;
      tracking_number : N;
      instrument_identification_code_type : list byte;
      instrument_identification_code : list byte;
      agreement_date : N;
      agreement_time : N;
      price_otc : N;
      price_fraction : N;
      price_notation : list byte;
      price_currency : list byte;
      quantity : N;
      quantity_fraction : N;
      notation_of_the_quantity_in_measurement_unit : list byte;
      quantity_in_measurement_unit : N;
      quantity_in_measurement_unit_fraction : N;
      venue_of_execution : list byte;
      notional_amount : N;
      notional_amount_fraction : N;
      notional_currency : list byte;
      type : list byte;
      transaction_identifier_code : list byte;
      mmt_trade_flags : list byte;
      transaction_to_be_cleared : list byte;
      trade_type : list byte;
      third_country_trading_venue_of_execution : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (instrument_identification_code_type record) = 4 /\
      Datatypes.length (instrument_identification_code record) = 12 /\
      (agreement_date record < 256 ^ N.of_nat 4)%N /\
      (agreement_time record < 256 ^ N.of_nat 8)%N /\
      (price_otc record < 256 ^ N.of_nat 8)%N /\
      (price_fraction record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (price_notation record) = 4 /\
      Datatypes.length (price_currency record) = 3 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (quantity_fraction record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (notation_of_the_quantity_in_measurement_unit record) = 25 /\
      (quantity_in_measurement_unit record < 256 ^ N.of_nat 8)%N /\
      (quantity_in_measurement_unit_fraction record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (venue_of_execution record) = 4 /\
      (notional_amount record < 256 ^ N.of_nat 8)%N /\
      (notional_amount_fraction record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (type record) = 4 /\
      Datatypes.length (transaction_identifier_code record) = 10 /\
      Datatypes.length (mmt_trade_flags record) = 14 /\
      Datatypes.length (transaction_to_be_cleared record) = 1 /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (third_country_trading_venue_of_execution record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 2 (tracking_number record) ++
      encode_bytes 4 (instrument_identification_code_type record) ++
      encode_bytes 12 (instrument_identification_code record) ++
      encode_uint 4 (agreement_date record) ++
      encode_uint 8 (agreement_time record) ++
      encode_uint 8 (price_otc record) ++
      encode_uint 1 (price_fraction record) ++
      encode_bytes 4 (price_notation record) ++
      encode_bytes 3 (price_currency record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 1 (quantity_fraction record) ++
      encode_bytes 25 (notation_of_the_quantity_in_measurement_unit record) ++
      encode_uint 8 (quantity_in_measurement_unit record) ++
      encode_uint 1 (quantity_in_measurement_unit_fraction record) ++
      encode_bytes 4 (venue_of_execution record) ++
      encode_uint 8 (notional_amount record) ++
      encode_uint 1 (notional_amount_fraction record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 4 (type record) ++
      encode_bytes 10 (transaction_identifier_code record) ++
      encode_bytes 14 (mmt_trade_flags record) ++
      encode_bytes 1 (transaction_to_be_cleared record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 4 (third_country_trading_venue_of_execution record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (tracking_number_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_identification_code_type_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (instrument_identification_code_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (agreement_date_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (agreement_time_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_otc_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (price_fraction_value, bytes) =>
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (price_notation_value, bytes) =>
                                          match decode_bytes 3 bytes with
                                          | None => None
                                          | Some (price_currency_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (quantity_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (quantity_fraction_value, bytes) =>
                                                      match decode_bytes 25 bytes with
                                                      | None => None
                                                      | Some (notation_of_the_quantity_in_measurement_unit_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (quantity_in_measurement_unit_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (quantity_in_measurement_unit_fraction_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (venue_of_execution_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (notional_amount_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (notional_amount_fraction_value, bytes) =>
                                                                              match decode_bytes 3 bytes with
                                                                              | None => None
                                                                              | Some (notional_currency_value, bytes) =>
                                                                                  match decode_bytes 4 bytes with
                                                                                  | None => None
                                                                                  | Some (type_value, bytes) =>
                                                                                      match decode_bytes 10 bytes with
                                                                                      | None => None
                                                                                      | Some (transaction_identifier_code_value, bytes) =>
                                                                                          match decode_bytes 14 bytes with
                                                                                          | None => None
                                                                                          | Some (mmt_trade_flags_value, bytes) =>
                                                                                              match decode_bytes 1 bytes with
                                                                                              | None => None
                                                                                              | Some (transaction_to_be_cleared_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (trade_type_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (third_country_trading_venue_of_execution_value, bytes) =>
                                                                                                          Some ({| timestamp := timestamp_value; tracking_number := tracking_number_value; instrument_identification_code_type := instrument_identification_code_type_value; instrument_identification_code := instrument_identification_code_value; agreement_date := agreement_date_value; agreement_time := agreement_time_value; price_otc := price_otc_value; price_fraction := price_fraction_value; price_notation := price_notation_value; price_currency := price_currency_value; quantity := quantity_value; quantity_fraction := quantity_fraction_value; notation_of_the_quantity_in_measurement_unit := notation_of_the_quantity_in_measurement_unit_value; quantity_in_measurement_unit := quantity_in_measurement_unit_value; quantity_in_measurement_unit_fraction := quantity_in_measurement_unit_fraction_value; venue_of_execution := venue_of_execution_value; notional_amount := notional_amount_value; notional_amount_fraction := notional_amount_fraction_value; notional_currency := notional_currency_value; type := type_value; transaction_identifier_code := transaction_identifier_code_value; mmt_trade_flags := mmt_trade_flags_value; transaction_to_be_cleared := transaction_to_be_cleared_value; trade_type := trade_type_value; third_country_trading_venue_of_execution := third_country_trading_venue_of_execution_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 147.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OtcTradeMessage.

End NordicEquitiesLastSaleV1211.
