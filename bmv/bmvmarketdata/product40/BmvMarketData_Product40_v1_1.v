From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Product 40

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

Module BmvMarketDataProduct40V11.

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
      (message_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 2 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  Module CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.

    (** It disseminates information on the local and global stock market. *)
    Record t := {
      instrument_number : N;
      value_type : list byte;
      issuer : list byte;
      series : list byte;
      last_price : N;
      wap : N;
      closing_price : N;
      reference_date : N;
      reference : list byte;
      current_coupon : N;
      marketability : list byte;
      numeric_marketability : N;
      isin : list byte;
      market : list byte;
      shares_outstanding : N;
      blocks_amount : N;
      exchange : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (value_type record) = 2 /\
      Datatypes.length (issuer record) = 7 /\
      Datatypes.length (series record) = 6 /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (wap record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (reference_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference record) = 2 /\
      (current_coupon record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (marketability record) = 2 /\
      (numeric_marketability record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (market record) = 1 /\
      (shares_outstanding record < 256 ^ N.of_nat 8)%N /\
      (blocks_amount record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exchange record) = 1 /\
      Datatypes.length (filler record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (value_type record) ++
      encode_bytes 7 (issuer record) ++
      encode_bytes 6 (series record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (wap record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 8 (reference_date record) ++
      encode_bytes 2 (reference record) ++
      encode_uint 2 (current_coupon record) ++
      encode_bytes 2 (marketability record) ++
      encode_uint 4 (numeric_marketability record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 1 (market record) ++
      encode_uint 8 (shares_outstanding record) ++
      encode_uint 8 (blocks_amount record) ++
      encode_bytes 1 (exchange record) ++
      encode_bytes 20 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (value_type_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (issuer_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (wap_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (closing_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (reference_date_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (reference_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (current_coupon_value, bytes) =>
                                              match decode_bytes 2 bytes with
                                              | None => None
                                              | Some (marketability_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (numeric_marketability_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (isin_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (market_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (shares_outstanding_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (blocks_amount_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (exchange_value, bytes) =>
                                                                          match decode_bytes 20 bytes with
                                                                          | None => None
                                                                          | Some (filler_value, bytes) =>
                                                                              Some ({| instrument_number := instrument_number_value; value_type := value_type_value; issuer := issuer_value; series := series_value; last_price := last_price_value; wap := wap_value; closing_price := closing_price_value; reference_date := reference_date_value; reference := reference_value; current_coupon := current_coupon_value; marketability := marketability_value; numeric_marketability := numeric_marketability_value; isin := isin_value; market := market_value; shares_outstanding := shares_outstanding_value; blocks_amount := blocks_amount_value; exchange := exchange_value; filler := filler_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 111.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogForInstrumentsBelongingToTheLocalAndGlobalStockMarketMessage.

  Module CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage.

    (** Catalog of instruments that belong to the Debt, Metals and Money market *)
    Record t := {
      instrument_number : N;
      value_type : list byte;
      issuer : list byte;
      issue : list byte;
      issue_date : N;
      maturity_date : N;
      reference_pricerate : N;
      reference_date : N;
      reference : list byte;
      term_days : N;
      current_coupon : N;
      isin : list byte;
      market : list byte;
      current_nominal_value : N;
      original_nominal_value : N;
      outstanding_shares : N;
      amount_placed : N;
      operate_price_rate : list byte;
      exchange : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (value_type record) = 2 /\
      Datatypes.length (issuer record) = 7 /\
      Datatypes.length (issue record) = 6 /\
      (issue_date record < 256 ^ N.of_nat 8)%N /\
      (maturity_date record < 256 ^ N.of_nat 8)%N /\
      (reference_pricerate record < 256 ^ N.of_nat 8)%N /\
      (reference_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference record) = 2 /\
      (term_days record < 256 ^ N.of_nat 2)%N /\
      (current_coupon record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (market record) = 1 /\
      (current_nominal_value record < 256 ^ N.of_nat 8)%N /\
      (original_nominal_value record < 256 ^ N.of_nat 8)%N /\
      (outstanding_shares record < 256 ^ N.of_nat 8)%N /\
      (amount_placed record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (operate_price_rate record) = 1 /\
      Datatypes.length (exchange record) = 1 /\
      Datatypes.length (filler record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (value_type record) ++
      encode_bytes 7 (issuer record) ++
      encode_bytes 6 (issue record) ++
      encode_uint 8 (issue_date record) ++
      encode_uint 8 (maturity_date record) ++
      encode_uint 8 (reference_pricerate record) ++
      encode_uint 8 (reference_date record) ++
      encode_bytes 2 (reference record) ++
      encode_uint 2 (term_days record) ++
      encode_uint 2 (current_coupon record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 1 (market record) ++
      encode_uint 8 (current_nominal_value record) ++
      encode_uint 8 (original_nominal_value record) ++
      encode_uint 8 (outstanding_shares record) ++
      encode_uint 8 (amount_placed record) ++
      encode_bytes 1 (operate_price_rate record) ++
      encode_bytes 1 (exchange record) ++
      encode_bytes 20 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (value_type_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (issuer_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (issue_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (issue_date_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (maturity_date_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (reference_pricerate_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (reference_date_value, bytes) =>
                                      match decode_bytes 2 bytes with
                                      | None => None
                                      | Some (reference_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (term_days_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (current_coupon_value, bytes) =>
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
                                                                          | Some (operate_price_rate_value, bytes) =>
                                                                              match decode_bytes 1 bytes with
                                                                              | None => None
                                                                              | Some (exchange_value, bytes) =>
                                                                                  match decode_bytes 20 bytes with
                                                                                  | None => None
                                                                                  | Some (filler_value, bytes) =>
                                                                                      Some ({| instrument_number := instrument_number_value; value_type := value_type_value; issuer := issuer_value; issue := issue_value; issue_date := issue_date_value; maturity_date := maturity_date_value; reference_pricerate := reference_pricerate_value; reference_date := reference_date_value; reference := reference_value; term_days := term_days_value; current_coupon := current_coupon_value; isin := isin_value; market := market_value; current_nominal_value := current_nominal_value_value; original_nominal_value := original_nominal_value_value; outstanding_shares := outstanding_shares_value; amount_placed := amount_placed_value; operate_price_rate := operate_price_rate_value; exchange := exchange_value; filler := filler_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 124.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 bound_19]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogOfInstrumentsThatBelongToTheDebtMetalsAndMoneyMarketMessage.

  Module CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.

    (** Catalog for instruments belonging to the capital warrants market *)
    Record t := {
      instrument_number : N;
      value_type : list byte;
      issuer : list byte;
      series : list byte;
      warrant_type : list byte;
      maturity_date : N;
      exercise_price : N;
      reference_price : N;
      reference_date : N;
      reference : list byte;
      isin : list byte;
      exchange : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (value_type record) = 2 /\
      Datatypes.length (issuer record) = 7 /\
      Datatypes.length (series record) = 6 /\
      Datatypes.length (warrant_type record) = 1 /\
      (maturity_date record < 256 ^ N.of_nat 8)%N /\
      (exercise_price record < 256 ^ N.of_nat 8)%N /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (reference_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference record) = 2 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (exchange record) = 1 /\
      Datatypes.length (filler record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (value_type record) ++
      encode_bytes 7 (issuer record) ++
      encode_bytes 6 (series record) ++
      encode_bytes 1 (warrant_type record) ++
      encode_uint 8 (maturity_date record) ++
      encode_uint 8 (exercise_price record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (reference_date record) ++
      encode_bytes 2 (reference record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 1 (exchange record) ++
      encode_bytes 20 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (value_type_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (issuer_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (warrant_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (maturity_date_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (exercise_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (reference_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (reference_date_value, bytes) =>
                                          match decode_bytes 2 bytes with
                                          | None => None
                                          | Some (reference_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (isin_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (exchange_value, bytes) =>
                                                      match decode_bytes 20 bytes with
                                                      | None => None
                                                      | Some (filler_value, bytes) =>
                                                          Some ({| instrument_number := instrument_number_value; value_type := value_type_value; issuer := issuer_value; series := series_value; warrant_type := warrant_type_value; maturity_date := maturity_date_value; exercise_price := exercise_price_value; reference_price := reference_price_value; reference_date := reference_date_value; reference := reference_value; isin := isin_value; exchange := exchange_value; filler := filler_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 87.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogForInstrumentsBelongingToTheCapitalWarrantsMarketMessage.

  Module OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage.

    (** Options, futures and swaps derivatives market instruments catalog *)
    Record t := {
      instrument_number : N;
      value_type : list byte;
      class : list byte;
      maturity : list byte;
      option_type : list byte;
      exercise_price : N;
      bid : N;
      prior_day_settlement_price : N;
      last_day_of_operation : N;
      maturity_date : N;
      open_contracts : N;
      contract_size : N;
      product_code : list byte;
      daily_maturity : list byte;
      key_exercise_price : list byte;
      cfi_code : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (value_type record) = 2 /\
      Datatypes.length (class record) = 7 /\
      Datatypes.length (maturity record) = 6 /\
      Datatypes.length (option_type record) = 1 /\
      (exercise_price record < 256 ^ N.of_nat 8)%N /\
      (bid record < 256 ^ N.of_nat 8)%N /\
      (prior_day_settlement_price record < 256 ^ N.of_nat 8)%N /\
      (last_day_of_operation record < 256 ^ N.of_nat 8)%N /\
      (maturity_date record < 256 ^ N.of_nat 8)%N /\
      (open_contracts record < 256 ^ N.of_nat 4)%N /\
      (contract_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (product_code record) = 12 /\
      Datatypes.length (daily_maturity record) = 1 /\
      Datatypes.length (key_exercise_price record) = 6 /\
      Datatypes.length (cfi_code record) = 6 /\
      Datatypes.length (filler record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (value_type record) ++
      encode_bytes 7 (class record) ++
      encode_bytes 6 (maturity record) ++
      encode_bytes 1 (option_type record) ++
      encode_uint 8 (exercise_price record) ++
      encode_uint 8 (bid record) ++
      encode_uint 8 (prior_day_settlement_price record) ++
      encode_uint 8 (last_day_of_operation record) ++
      encode_uint 8 (maturity_date record) ++
      encode_uint 4 (open_contracts record) ++
      encode_uint 4 (contract_size record) ++
      encode_bytes 12 (product_code record) ++
      encode_bytes 1 (daily_maturity record) ++
      encode_bytes 6 (key_exercise_price record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_bytes 20 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (value_type_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (class_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (maturity_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (option_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (exercise_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (bid_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (prior_day_settlement_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_day_of_operation_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (maturity_date_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (open_contracts_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (contract_size_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (product_code_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (daily_maturity_value, bytes) =>
                                                              match decode_bytes 6 bytes with
                                                              | None => None
                                                              | Some (key_exercise_price_value, bytes) =>
                                                                  match decode_bytes 6 bytes with
                                                                  | None => None
                                                                  | Some (cfi_code_value, bytes) =>
                                                                      match decode_bytes 20 bytes with
                                                                      | None => None
                                                                      | Some (filler_value, bytes) =>
                                                                          Some ({| instrument_number := instrument_number_value; value_type := value_type_value; class := class_value; maturity := maturity_value; option_type := option_type_value; exercise_price := exercise_price_value; bid := bid_value; prior_day_settlement_price := prior_day_settlement_price_value; last_day_of_operation := last_day_of_operation_value; maturity_date := maturity_date_value; open_contracts := open_contracts_value; contract_size := contract_size_value; product_code := product_code_value; daily_maturity := daily_maturity_value; key_exercise_price := key_exercise_price_value; cfi_code := cfi_code_value; filler := filler_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 113.
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
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsFuturesAndSwapsDerivativesMarketInstrumentsCatalogMessage.

  Module CatalogSentForInstrumentsBelongingToCapitalTracsMessage.

    (** Catalog sent for instruments belonging to capital TRACS *)
    Record t := {
      trac_number : N;
      trac_name : list byte;
      underlying_issuer : list byte;
      underlying_series : list byte;
      securities : N;
      excluded_securities : N;
      price : N;
      cash_component : N;
      excluded_value : N;
      number_of_certificates : N;
      theoretical_price : N;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trac_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trac_name record) = 8 /\
      Datatypes.length (underlying_issuer record) = 7 /\
      Datatypes.length (underlying_series record) = 6 /\
      (securities record < 256 ^ N.of_nat 8)%N /\
      (excluded_securities record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (cash_component record < 256 ^ N.of_nat 8)%N /\
      (excluded_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_certificates record < 256 ^ N.of_nat 8)%N /\
      (theoretical_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (filler record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trac_number record) ++
      encode_bytes 8 (trac_name record) ++
      encode_bytes 7 (underlying_issuer record) ++
      encode_bytes 6 (underlying_series record) ++
      encode_uint 8 (securities record) ++
      encode_uint 8 (excluded_securities record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (cash_component record) ++
      encode_uint 8 (excluded_value record) ++
      encode_uint 8 (number_of_certificates record) ++
      encode_uint 8 (theoretical_price record) ++
      encode_bytes 20 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (trac_number_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (trac_name_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (underlying_issuer_value, bytes) =>
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
                                  | Some (cash_component_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (excluded_value_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (number_of_certificates_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (theoretical_price_value, bytes) =>
                                                  match decode_bytes 20 bytes with
                                                  | None => None
                                                  | Some (filler_value, bytes) =>
                                                      Some ({| trac_number := trac_number_value; trac_name := trac_name_value; underlying_issuer := underlying_issuer_value; underlying_series := underlying_series_value; securities := securities_value; excluded_securities := excluded_securities_value; price := price_value; cash_component := cash_component_value; excluded_value := excluded_value_value; number_of_certificates := number_of_certificates_value; theoretical_price := theoretical_price_value; filler := filler_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 101.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogSentForInstrumentsBelongingToCapitalTracsMessage.

  Module CatalogSentForInstrumentsBelongingToMutualFundsMessage.

    (** Catalog sent for instruments belonging to mutual funds *)
    Record t := {
      instrument_number : N;
      value_type : list byte;
      issuer : list byte;
      series : list byte;
      sector : N;
      subsector : N;
      business_line : N;
      sub_line : N;
      operating_company : list byte;
      reference_price : N;
      reference_date : N;
      reference : list byte;
      isin : list byte;
      rating : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (value_type record) = 2 /\
      Datatypes.length (issuer record) = 7 /\
      Datatypes.length (series record) = 6 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (subsector record < 256 ^ N.of_nat 1)%N /\
      (business_line record < 256 ^ N.of_nat 1)%N /\
      (sub_line record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (operating_company record) = 10 /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (reference_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference record) = 2 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (rating record) = 15 /\
      Datatypes.length (filler record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (value_type record) ++
      encode_bytes 7 (issuer record) ++
      encode_bytes 6 (series record) ++
      encode_uint 1 (sector record) ++
      encode_uint 1 (subsector record) ++
      encode_uint 1 (business_line record) ++
      encode_uint 1 (sub_line record) ++
      encode_bytes 10 (operating_company record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 8 (reference_date record) ++
      encode_bytes 2 (reference record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 15 (rating record) ++
      encode_bytes 20 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (value_type_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (issuer_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (series_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (sector_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (subsector_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (business_line_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (sub_line_value, bytes) =>
                                      match decode_bytes 10 bytes with
                                      | None => None
                                      | Some (operating_company_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (reference_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (reference_date_value, bytes) =>
                                                  match decode_bytes 2 bytes with
                                                  | None => None
                                                  | Some (reference_value, bytes) =>
                                                      match decode_bytes 12 bytes with
                                                      | None => None
                                                      | Some (isin_value, bytes) =>
                                                          match decode_bytes 15 bytes with
                                                          | None => None
                                                          | Some (rating_value, bytes) =>
                                                              match decode_bytes 20 bytes with
                                                              | None => None
                                                              | Some (filler_value, bytes) =>
                                                                  Some ({| instrument_number := instrument_number_value; value_type := value_type_value; issuer := issuer_value; series := series_value; sector := sector_value; subsector := subsector_value; business_line := business_line_value; sub_line := sub_line_value; operating_company := operating_company_value; reference_price := reference_price_value; reference_date := reference_date_value; reference := reference_value; isin := isin_value; rating := rating_value; filler := filler_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 98.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogSentForInstrumentsBelongingToMutualFundsMessage.

  Module CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage.

    (** Catalog sent for instruments belonging to the strategy derivative market *)
    Record t := {
      instrument_number : N;
      value_type : list byte;
      class : list byte;
      maturity : list byte;
      type_of_strategy : list byte;
      bid : N;
      last_date_operation : N;
      maturity_date : N;
      short_leg_instrument_identifier : N;
      long_leg_instruments_id : N;
      frequency : N;
      number_of_maturities : N;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (value_type record) = 2 /\
      Datatypes.length (class record) = 7 /\
      Datatypes.length (maturity record) = 6 /\
      Datatypes.length (type_of_strategy record) = 1 /\
      (bid record < 256 ^ N.of_nat 8)%N /\
      (last_date_operation record < 256 ^ N.of_nat 8)%N /\
      (maturity_date record < 256 ^ N.of_nat 8)%N /\
      (short_leg_instrument_identifier record < 256 ^ N.of_nat 4)%N /\
      (long_leg_instruments_id record < 256 ^ N.of_nat 4)%N /\
      (frequency record < 256 ^ N.of_nat 1)%N /\
      (number_of_maturities record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (filler record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 2 (value_type record) ++
      encode_bytes 7 (class record) ++
      encode_bytes 6 (maturity record) ++
      encode_bytes 1 (type_of_strategy record) ++
      encode_uint 8 (bid record) ++
      encode_uint 8 (last_date_operation record) ++
      encode_uint 8 (maturity_date record) ++
      encode_uint 4 (short_leg_instrument_identifier record) ++
      encode_uint 4 (long_leg_instruments_id record) ++
      encode_uint 1 (frequency record) ++
      encode_uint 1 (number_of_maturities record) ++
      encode_bytes 20 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (value_type_value, bytes) =>
              match decode_bytes 7 bytes with
              | None => None
              | Some (class_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (maturity_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (type_of_strategy_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (bid_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (last_date_operation_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (maturity_date_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (short_leg_instrument_identifier_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (long_leg_instruments_id_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (frequency_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (number_of_maturities_value, bytes) =>
                                                      match decode_bytes 20 bytes with
                                                      | None => None
                                                      | Some (filler_value, bytes) =>
                                                          Some ({| instrument_number := instrument_number_value; value_type := value_type_value; class := class_value; maturity := maturity_value; type_of_strategy := type_of_strategy_value; bid := bid_value; last_date_operation := last_date_operation_value; maturity_date := maturity_date_value; short_leg_instrument_identifier := short_leg_instrument_identifier_value; long_leg_instruments_id := long_leg_instruments_id_value; frequency := frequency_value; number_of_maturities := number_of_maturities_value; filler := filler_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CatalogSentForInstrumentsBelongingToTheStrategyDerivativeMarketMessage.

  Module UnderlyingValueOnWarrantsCatalogMessage.

    (** Underlying value on warrants catalog *)
    Record t := {
      instrument_number : N;
      issuer : list byte;
      series : list byte;
      value_type : list byte;
      underlying_issuer : list byte;
      underlying_series : list byte;
      underlying_value_type : list byte;
      number_of_registered_values : N;
      exchange : list byte;
      filler : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (issuer record) = 7 /\
      Datatypes.length (series record) = 6 /\
      Datatypes.length (value_type record) = 2 /\
      Datatypes.length (underlying_issuer record) = 7 /\
      Datatypes.length (underlying_series record) = 6 /\
      Datatypes.length (underlying_value_type record) = 2 /\
      (number_of_registered_values record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (exchange record) = 1 /\
      Datatypes.length (filler record) = 20.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 7 (issuer record) ++
      encode_bytes 6 (series record) ++
      encode_bytes 2 (value_type record) ++
      encode_bytes 7 (underlying_issuer record) ++
      encode_bytes 6 (underlying_series record) ++
      encode_bytes 2 (underlying_value_type record) ++
      encode_uint 8 (number_of_registered_values record) ++
      encode_bytes 1 (exchange record) ++
      encode_bytes 20 (filler record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 7 bytes with
          | None => None
          | Some (issuer_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (series_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (value_type_value, bytes) =>
                      match decode_bytes 7 bytes with
                      | None => None
                      | Some (underlying_issuer_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (underlying_series_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (underlying_value_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (number_of_registered_values_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (exchange_value, bytes) =>
                                          match decode_bytes 20 bytes with
                                          | None => None
                                          | Some (filler_value, bytes) =>
                                              Some ({| instrument_number := instrument_number_value; issuer := issuer_value; series := series_value; value_type := value_type_value; underlying_issuer := underlying_issuer_value; underlying_series := underlying_series_value; underlying_value_type := underlying_value_type_value; number_of_registered_values := number_of_registered_values_value; exchange := exchange_value; filler := filler_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingValueOnWarrantsCatalogMessage.

End BmvMarketDataProduct40V11.
