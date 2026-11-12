From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Product 26

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

    License: MIT No Attribution
  *)

Module BmvMarketDataProduct26V11.

  Module INTRAMulticastHeader.

    (** BMV INTRA Multicast Header *)
    Record t := {
      length_ : N;
      total_messages : N;
      market_data_group : N;
      session : N;
      sequence_number : N;
      datetime : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (total_messages record < 256 ^ N.of_nat 1)%N /\
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (session record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (datetime record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (total_messages record) ++
      encode_uint 1 (market_data_group record) ++
      encode_uint 1 (session record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (datetime record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (total_messages_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (sequence_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (datetime_value, bytes) =>
                              Some ({| length_ := length__value; total_messages := total_messages_value; market_data_group := market_data_group_value; session := session_value; sequence_number := sequence_number_value; datetime := datetime_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End INTRAMulticastHeader.

  Module MessageHeader.

    (** Message length and message type *)
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

  Module MutualFundsTradesMessage.

    (** Any transaction made in mutual funds is reported. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      date_of_the_trade : N;
      price : N;
      book_value : N;
      number_of_sales_trades : N;
      sales_volume : N;
      number_of_purchase_trades : N;
      purchase_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (date_of_the_trade record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (book_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_sales_trades record < 256 ^ N.of_nat 4)%N /\
      (sales_volume record < 256 ^ N.of_nat 8)%N /\
      (number_of_purchase_trades record < 256 ^ N.of_nat 4)%N /\
      (purchase_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (date_of_the_trade record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (book_value record) ++
      encode_uint 4 (number_of_sales_trades record) ++
      encode_uint 8 (sales_volume record) ++
      encode_uint 4 (number_of_purchase_trades record) ++
      encode_uint 8 (purchase_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (date_of_the_trade_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (book_value_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (number_of_sales_trades_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (sales_volume_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (number_of_purchase_trades_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (purchase_volume_value, bytes) =>
                                          Some ({| instrument_number := instrument_number_value; origin := origin_value; date_of_the_trade := date_of_the_trade_value; price := price_value; book_value := book_value_value; number_of_sales_trades := number_of_sales_trades_value; sales_volume := sales_volume_value; number_of_purchase_trades := number_of_purchase_trades_value; purchase_volume := purchase_volume_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MutualFundsTradesMessage.

  Module OpeningOfContinuousAuctionsMessage.

    (** The message is sent when one of the ongoing, volatility or SIC bidding sessions is generated. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      auction_session_startup_time : N;
      auction_session_end_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (auction_session_startup_time record < 256 ^ N.of_nat 8)%N /\
      (auction_session_end_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (auction_session_startup_time record) ++
      encode_uint 8 (auction_session_end_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (auction_session_startup_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (auction_session_end_time_value, bytes) =>
                      Some ({| instrument_number := instrument_number_value; origin := origin_value; auction_session_startup_time := auction_session_startup_time_value; auction_session_end_time := auction_session_end_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End OpeningOfContinuousAuctionsMessage.

  Module ExistenceOfBidsAtMidPriceMessage.

    (** This message is generated when an instrument enters a bid in the hidden electronic book At Mean Price. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      bids_existing : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (bids_existing record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 1 (bids_existing record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (bids_existing_value, bytes) =>
                  Some ({| instrument_number := instrument_number_value; origin := origin_value; bids_existing := bids_existing_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExistenceOfBidsAtMidPriceMessage.

  Module CatalogueOfDebtAndMetalsInstrumentsMessage.

    (** Catalogue sent for instruments pertaining to the Local Fixed rate, Global Fixed rate and metals markets. *)
    Record t := {
      number_of_the_instrument : N;
      origin : list byte;
      type_of_value : list byte;
      issuing_company : list byte;
      issuance : list byte;
      date_of_issuance : N;
      date_of_maturity : N;
      price_rate_of_reference : N;
      date_of_reference : N;
      reference : list byte;
      term_days : N;
      coupon_period : N;
      isin : list byte;
      market : list byte;
      current_nominal_value : N;
      original_nominal_value : N;
      outstanding_shares : N;
      amount_placed : N;
      trades_rate_price : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_the_instrument record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (type_of_value record) = 2 /\
      Datatypes.length (issuing_company record) = 7 /\
      Datatypes.length (issuance record) = 6 /\
      (date_of_issuance record < 256 ^ N.of_nat 8)%N /\
      (date_of_maturity record < 256 ^ N.of_nat 8)%N /\
      (price_rate_of_reference record < 256 ^ N.of_nat 8)%N /\
      (date_of_reference record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference record) = 1 /\
      (term_days record < 256 ^ N.of_nat 2)%N /\
      (coupon_period record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (market record) = 1 /\
      (current_nominal_value record < 256 ^ N.of_nat 8)%N /\
      (original_nominal_value record < 256 ^ N.of_nat 8)%N /\
      (outstanding_shares record < 256 ^ N.of_nat 8)%N /\
      (amount_placed record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trades_rate_price record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_the_instrument record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 2 (type_of_value record) ++
      encode_bytes 7 (issuing_company record) ++
      encode_bytes 6 (issuance record) ++
      encode_uint 8 (date_of_issuance record) ++
      encode_uint 8 (date_of_maturity record) ++
      encode_uint 8 (price_rate_of_reference record) ++
      encode_uint 8 (date_of_reference record) ++
      encode_bytes 1 (reference record) ++
      encode_uint 2 (term_days record) ++
      encode_uint 2 (coupon_period record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 1 (market record) ++
      encode_uint 8 (current_nominal_value record) ++
      encode_uint 8 (original_nominal_value record) ++
      encode_uint 8 (outstanding_shares record) ++
      encode_uint 8 (amount_placed record) ++
      encode_bytes 1 (trades_rate_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_the_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (type_of_value_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (issuing_company_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (issuance_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (date_of_issuance_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (date_of_maturity_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_rate_of_reference_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (date_of_reference_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (reference_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (term_days_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (coupon_period_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (isin_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (market_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (current_nominal_value_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (original_nominal_value_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (outstanding_shares_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (amount_placed_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (trades_rate_price_value, bytes) =>
                                                                                  Some ({| number_of_the_instrument := number_of_the_instrument_value; origin := origin_value; type_of_value := type_of_value_value; issuing_company := issuing_company_value; issuance := issuance_value; date_of_issuance := date_of_issuance_value; date_of_maturity := date_of_maturity_value; price_rate_of_reference := price_rate_of_reference_value; date_of_reference := date_of_reference_value; reference := reference_value; term_days := term_days_value; coupon_period := coupon_period_value; isin := isin_value; market := market_value; current_nominal_value := current_nominal_value_value; original_nominal_value := original_nominal_value_value; outstanding_shares := outstanding_shares_value; amount_placed := amount_placed_value; trades_rate_price := trades_rate_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 103.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogueOfDebtAndMetalsInstrumentsMessage.

  Module CatalogSentForInstrumentsBelongingToMutualFundsMessage.

    (** Catalogue sent for instrument pertaining to the investment companies. *)
    Record t := {
      number_of_the_instrument : N;
      origin : list byte;
      type_of_value : list byte;
      issuing_company : list byte;
      series : list byte;
      sector : N;
      sub_sector : N;
      industry : N;
      sub_industry : N;
      trading_company : list byte;
      reference_price : N;
      reference_date : N;
      reference : list byte;
      isin : list byte;
      rating : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_the_instrument record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (type_of_value record) = 2 /\
      Datatypes.length (issuing_company record) = 7 /\
      Datatypes.length (series record) = 6 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (sub_sector record < 256 ^ N.of_nat 1)%N /\
      (industry record < 256 ^ N.of_nat 1)%N /\
      (sub_industry record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trading_company record) = 10 /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (reference_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference record) = 1 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (rating record) = 15.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_the_instrument record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 2 (type_of_value record) ++
      encode_bytes 7 (issuing_company record) ++
      encode_bytes 6 (series record) ++
      encode_uint 1 (sector record) ++
      encode_uint 1 (sub_sector record) ++
      encode_uint 1 (industry record) ++
      encode_uint 1 (sub_industry record) ++
      encode_bytes 10 (trading_company record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (reference_date record) ++
      encode_bytes 1 (reference record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 15 (rating record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_the_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (type_of_value_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (issuing_company_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (series_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (sector_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (sub_sector_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (industry_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (sub_industry_value, bytes) =>
                                          match decode_bytes 10 bytes with
                                          | None => None
                                          | Some (trading_company_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (reference_price_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (reference_date_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (reference_value, bytes) =>
                                                          match decode_bytes 12 bytes with
                                                          | None => None
                                                          | Some (isin_value, bytes) =>
                                                              match decode_bytes 15 bytes with
                                                              | None => None
                                                              | Some (rating_value, bytes) =>
                                                                  Some ({| number_of_the_instrument := number_of_the_instrument_value; origin := origin_value; type_of_value := type_of_value_value; issuing_company := issuing_company_value; series := series_value; sector := sector_value; sub_sector := sub_sector_value; industry := industry_value; sub_industry := sub_industry_value; trading_company := trading_company_value; reference_price := reference_price_value; reference_date := reference_date_value; reference := reference_value; isin := isin_value; rating := rating_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 78.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogSentForInstrumentsBelongingToMutualFundsMessage.

  Module WeightedAveragePriceMessage.

    (** This message will have the weighted average price (WAP) per instrument and is sent for each transaction generated within the calculation period of the WAP (last 20 minutes of the trading session); when there are no more trades in this period, the message is sent with the Weighted Average Price in zeros. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      weighted_average_price : N;
      volatility : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (weighted_average_price record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (weighted_average_price record) ++
      encode_uint 8 (volatility record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (weighted_average_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (volatility_value, bytes) =>
                      Some ({| instrument_number := instrument_number_value; origin := origin_value; weighted_average_price := weighted_average_price_value; volatility := volatility_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End WeightedAveragePriceMessage.

  Module SystemEventsMessage.

    (** The system events message is used to inform that an event has taken place, which needs to be disclosed to the public for its attention. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      code_of_event : list byte;
      market : list byte;
      send_time : N;
      end_time : N;
      group : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (code_of_event record) = 1 /\
      Datatypes.length (market record) = 1 /\
      (send_time record < 256 ^ N.of_nat 8)%N /\
      (end_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (group record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 1 (code_of_event record) ++
      encode_bytes 1 (market record) ++
      encode_uint 8 (send_time record) ++
      encode_uint 8 (end_time record) ++
      encode_bytes 8 (group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (code_of_event_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (market_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (send_time_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (end_time_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (group_value, bytes) =>
                                  Some ({| instrument_number := instrument_number_value; origin := origin_value; code_of_event := code_of_event_value; market := market_value; send_time := send_time_value; end_time := end_time_value; group := group_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventsMessage.

  Module ReferencePriceMessage.

    (** This message is sent to define the reference price of an instrument. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      price : N;
      price_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (price_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (price_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (price_type_value, bytes) =>
                      Some ({| instrument_number := instrument_number_value; origin := origin_value; price := price_value; price_type := price_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End ReferencePriceMessage.

  Module ChangesInStatusMessage.

    (** This message is sent when there has been a change in the status of the instruments. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      status : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (status record) = 1 /\
      Datatypes.length (reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 1 (status record) ++
      encode_bytes 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      Some ({| instrument_number := instrument_number_value; origin := origin_value; status := status_value; reason := reason_value |}, bytes)
                  end
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

  End ChangesInStatusMessage.

  Module CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.

    (** Catalogue for instruments pertaining to the Equities Warrants market. *)
    Record t := {
      number_of_the_instrument : N;
      origin : list byte;
      type_of_value : list byte;
      issuing_company : list byte;
      series : list byte;
      type_of_warrant : list byte;
      date_of_maturity : N;
      price_of_exercise : N;
      reference_price : N;
      reference_date : N;
      reference : list byte;
      isin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_the_instrument record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (type_of_value record) = 2 /\
      Datatypes.length (issuing_company record) = 7 /\
      Datatypes.length (series record) = 6 /\
      Datatypes.length (type_of_warrant record) = 1 /\
      (date_of_maturity record < 256 ^ N.of_nat 8)%N /\
      (price_of_exercise record < 256 ^ N.of_nat 8)%N /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (reference_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference record) = 1 /\
      Datatypes.length (isin record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_the_instrument record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 2 (type_of_value record) ++
      encode_bytes 7 (issuing_company record) ++
      encode_bytes 6 (series record) ++
      encode_bytes 1 (type_of_warrant record) ++
      encode_uint 8 (date_of_maturity record) ++
      encode_uint 8 (price_of_exercise record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (reference_date record) ++
      encode_bytes 1 (reference record) ++
      encode_bytes 12 (isin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_the_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (type_of_value_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (issuing_company_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (series_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (type_of_warrant_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (date_of_maturity_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_of_exercise_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (reference_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (reference_date_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (reference_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (isin_value, bytes) =>
                                                      Some ({| number_of_the_instrument := number_of_the_instrument_value; origin := origin_value; type_of_value := type_of_value_value; issuing_company := issuing_company_value; series := series_value; type_of_warrant := type_of_warrant_value; date_of_maturity := date_of_maturity_value; price_of_exercise := price_of_exercise_value; reference_price := reference_price_value; reference_date := reference_date_value; reference := reference_value; isin := isin_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
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

  End CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.

  Module CatalogSentForInstrumentsBelongingToCapitalTracsMessage.

    (** Catalogue sent for instruments pertaining to the equities TRACS. *)
    Record t := {
      number_of_the_trac : N;
      origin : list byte;
      name_of_the_trac : list byte;
      underlying_issuing_company : list byte;
      underlying_series : list byte;
      securities : N;
      excluded_securities : N;
      price : N;
      component_in_cash : N;
      excluded_value : N;
      number_of_certificates : N;
      theoretical_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_the_trac record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (name_of_the_trac record) = 8 /\
      Datatypes.length (underlying_issuing_company record) = 7 /\
      Datatypes.length (underlying_series record) = 6 /\
      (securities record < 256 ^ N.of_nat 8)%N /\
      (excluded_securities record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (component_in_cash record < 256 ^ N.of_nat 8)%N /\
      (excluded_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_certificates record < 256 ^ N.of_nat 8)%N /\
      (theoretical_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_the_trac record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 8 (name_of_the_trac record) ++
      encode_bytes 7 (underlying_issuing_company record) ++
      encode_bytes 6 (underlying_series record) ++
      encode_uint 8 (securities record) ++
      encode_uint 8 (excluded_securities record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (component_in_cash record) ++
      encode_uint 8 (excluded_value record) ++
      encode_uint 8 (number_of_certificates record) ++
      encode_uint 8 (theoretical_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_the_trac_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (name_of_the_trac_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (underlying_issuing_company_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (underlying_series_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (securities_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (excluded_securities_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (component_in_cash_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (excluded_value_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (number_of_certificates_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (theoretical_price_value, bytes) =>
                                                      Some ({| number_of_the_trac := number_of_the_trac_value; origin := origin_value; name_of_the_trac := name_of_the_trac_value; underlying_issuing_company := underlying_issuing_company_value; underlying_series := underlying_series_value; securities := securities_value; excluded_securities := excluded_securities_value; price := price_value; component_in_cash := component_in_cash_value; excluded_value := excluded_value_value; number_of_certificates := number_of_certificates_value; theoretical_price := theoretical_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 82.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
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

  End CatalogSentForInstrumentsBelongingToCapitalTracsMessage.

  Module ConsolidatedInavMessage.

    (** Disclosure of the TRACS during the trading hours of the ongoing market. *)
    Record t := {
      number_of_the_trac : N;
      origin : list byte;
      current_theoretical_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_the_trac record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (current_theoretical_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_the_trac record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (current_theoretical_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_the_trac_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (current_theoretical_price_value, bytes) =>
                  Some ({| number_of_the_trac := number_of_the_trac_value; origin := origin_value; current_theoretical_price := current_theoretical_price_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConsolidatedInavMessage.

  Module CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.

    (** Catalog of instruments from the local and global stock markets. *)
    Record t := {
      mse_instrument_number : N;
      value_of_type : list byte;
      issuing_company : list byte;
      series : list byte;
      last_price : N;
      ppp_weighted_average_price : N;
      reference_date : N;
      reference : list byte;
      coupon_in_effect : N;
      marketability : list byte;
      numerical_marketability : N;
      isin : list byte;
      market : list byte;
      registered_values : N;
      exchange : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mse_instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (value_of_type record) = 2 /\
      Datatypes.length (issuing_company record) = 7 /\
      Datatypes.length (series record) = 6 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (ppp_weighted_average_price record < 256 ^ N.of_nat 8)%N /\
      (reference_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference record) = 1 /\
      (coupon_in_effect record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (marketability record) = 1 /\
      (numerical_marketability record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (market record) = 1 /\
      (registered_values record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exchange record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (mse_instrument_number record) ++
      encode_bytes 2 (value_of_type record) ++
      encode_bytes 7 (issuing_company record) ++
      encode_bytes 6 (series record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (ppp_weighted_average_price record) ++
      encode_uint 8 (reference_date record) ++
      encode_bytes 1 (reference record) ++
      encode_uint 2 (coupon_in_effect record) ++
      encode_bytes 1 (marketability record) ++
      encode_uint 4 (numerical_marketability record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 1 (market record) ++
      encode_uint 8 (registered_values record) ++
      encode_bytes 1 (exchange record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (mse_instrument_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (value_of_type_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (issuing_company_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ppp_weighted_average_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (reference_date_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (reference_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (coupon_in_effect_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (marketability_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (numerical_marketability_value, bytes) =>
                                                  match decode_bytes 12 bytes with
                                                  | None => None
                                                  | Some (isin_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (market_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (registered_values_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (exchange_value, bytes) =>
                                                                  Some ({| mse_instrument_number := mse_instrument_number_value; value_of_type := value_of_type_value; issuing_company := issuing_company_value; series := series_value; last_price := last_price_value; ppp_weighted_average_price := ppp_weighted_average_price_value; reference_date := reference_date_value; reference := reference_value; coupon_in_effect := coupon_in_effect_value; marketability := marketability_value; numerical_marketability := numerical_marketability_value; isin := isin_value; market := market_value; registered_values := registered_values_value; exchange := exchange_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 73.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.

  Module ProbablePriceOfAllocationMessage.

    (** The message is sent during any type of bidding (Opening, Ongoing, Volatility and Intraday) and only in the instruments where there already is a virtual term matching or pre-allotment. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      probable_price_of_allocation : N;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (probable_price_of_allocation record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (probable_price_of_allocation record) ++
      encode_uint 8 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (probable_price_of_allocation_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      Some ({| instrument_number := instrument_number_value; origin := origin_value; probable_price_of_allocation := probable_price_of_allocation_value; volume := volume_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End ProbablePriceOfAllocationMessage.

  Module RelationBetweenBmvbivaInstrumentsMessage.

    (** Relation between identifiers of instruments between BIVA and BMV. *)
    Record t := {
      number_of_the_bmv_instrument : N;
      biva_instrument : N;
      type_of_trading : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (number_of_the_bmv_instrument record < 256 ^ N.of_nat 4)%N /\
      (biva_instrument record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (type_of_trading record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (number_of_the_bmv_instrument record) ++
      encode_uint 4 (biva_instrument record) ++
      encode_bytes 1 (type_of_trading record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (number_of_the_bmv_instrument_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (biva_instrument_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (type_of_trading_value, bytes) =>
                  Some ({| number_of_the_bmv_instrument := number_of_the_bmv_instrument_value; biva_instrument := biva_instrument_value; type_of_trading := type_of_trading_value |}, bytes)
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

  End RelationBetweenBmvbivaInstrumentsMessage.

  Module EquitiesMarketTradesMessage.

    (** Informs about any transaction which was accepted at the BMV or BIVA. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      time_of_the_trade : N;
      volume : N;
      price : N;
      type_of_agreement : list byte;
      consecutive_number_of_the_trade : N;
      sets_price : list byte;
      type_of_trading : list byte;
      amount : N;
      purchases : list byte;
      sells : list byte;
      settlement : list byte;
      auction_indicator : list byte;
      indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (time_of_the_trade record < 256 ^ N.of_nat 8)%N /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (type_of_agreement record) = 1 /\
      (consecutive_number_of_the_trade record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sets_price record) = 1 /\
      Datatypes.length (type_of_trading record) = 1 /\
      (amount record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (purchases record) = 5 /\
      Datatypes.length (sells record) = 5 /\
      Datatypes.length (settlement record) = 1 /\
      Datatypes.length (auction_indicator record) = 1 /\
      Datatypes.length (indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (time_of_the_trade record) ++
      encode_uint 8 (volume record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (type_of_agreement record) ++
      encode_uint 8 (consecutive_number_of_the_trade record) ++
      encode_bytes 1 (sets_price record) ++
      encode_bytes 1 (type_of_trading record) ++
      encode_uint 8 (amount record) ++
      encode_bytes 5 (purchases record) ++
      encode_bytes 5 (sells record) ++
      encode_bytes 1 (settlement record) ++
      encode_bytes 1 (auction_indicator record) ++
      encode_bytes 1 (indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (time_of_the_trade_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (type_of_agreement_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (consecutive_number_of_the_trade_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (sets_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (type_of_trading_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (amount_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (purchases_value, bytes) =>
                                                  match decode_bytes 5 bytes with
                                                  | None => None
                                                  | Some (sells_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (settlement_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (auction_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (indicator_value, bytes) =>
                                                                  Some ({| instrument_number := instrument_number_value; origin := origin_value; time_of_the_trade := time_of_the_trade_value; volume := volume_value; price := price_value; type_of_agreement := type_of_agreement_value; consecutive_number_of_the_trade := consecutive_number_of_the_trade_value; sets_price := sets_price_value; type_of_trading := type_of_trading_value; amount := amount_value; purchases := purchases_value; sells := sells_value; settlement := settlement_value; auction_indicator := auction_indicator_value; indicator := indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EquitiesMarketTradesMessage.

  Module ConsolidatedTradeCancellationMessage.

    (** This message in sent when a transaction is cancelled from BMV or BIVA system. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      consecutive_number_of_the_trade : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (consecutive_number_of_the_trade record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (consecutive_number_of_the_trade record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (consecutive_number_of_the_trade_value, bytes) =>
                  Some ({| instrument_number := instrument_number_value; origin := origin_value; consecutive_number_of_the_trade := consecutive_number_of_the_trade_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConsolidatedTradeCancellationMessage.

  Module LastQuoteMessage.

    (** Message sent by instrument when the best bid is modified in the electronic book by the Origin Exchange; denotes the side that is modified, the sale or the purchase. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      volume : N;
      price_rate : N;
      direction_of_the_bid : list byte;
      type_of_trading : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (price_rate record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (direction_of_the_bid record) = 1 /\
      Datatypes.length (type_of_trading record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (volume record) ++
      encode_uint 8 (price_rate record) ++
      encode_bytes 1 (direction_of_the_bid record) ++
      encode_bytes 1 (type_of_trading record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (volume_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_rate_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (direction_of_the_bid_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (type_of_trading_value, bytes) =>
                              Some ({| instrument_number := instrument_number_value; origin := origin_value; volume := volume_value; price_rate := price_rate_value; direction_of_the_bid := direction_of_the_bid_value; type_of_trading := type_of_trading_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastQuoteMessage.

End BmvMarketDataProduct26V11.
