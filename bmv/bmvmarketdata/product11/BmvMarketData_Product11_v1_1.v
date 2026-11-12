From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Product 11

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

Module BmvMarketDataProduct11V11.

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

  Module EventsSystemMessage.

    (** The system of events message is used to inform that an event has occurred, which needs to be of public domain. *)
    Record t := {
      instrument_number : N;
      event_code : list byte;
      market : list byte;
      sending_time : N;
      ending_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 1 /\
      Datatypes.length (market record) = 1 /\
      (sending_time record < 256 ^ N.of_nat 8)%N /\
      (ending_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (event_code record) ++
      encode_bytes 1 (market record) ++
      encode_uint 8 (sending_time record) ++
      encode_uint 8 (ending_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (sending_time_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (ending_time_value, bytes) =>
                          Some ({| instrument_number := instrument_number_value; event_code := event_code_value; market := market_value; sending_time := sending_time_value; ending_time := ending_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EventsSystemMessage.

  Module TradeCancellationMessage.

    (** This message is sent when a transaction is cancelled from the BMV system. *)
    Record t := {
      instrument_number : N;
      trade_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (trade_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 4 (trade_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trade_number_value, bytes) =>
              Some ({| instrument_number := instrument_number_value; trade_number := trade_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End TradeCancellationMessage.

  Module CapitalTradesMessage.

    (** Contains information on any BMV accepted transaction. *)
    Record t := {
      instrument_number : N;
      trade_time : N;
      volume_int_324 : N;
      price : N;
      concertation_type : list byte;
      trade_number : N;
      price_setter : list byte;
      operation_type : list byte;
      amount : N;
      buy : list byte;
      sell : list byte;
      settlement : list byte;
      auction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (trade_time record < 256 ^ N.of_nat 8)%N /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (concertation_type record) = 1 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (price_setter record) = 1 /\
      Datatypes.length (operation_type record) = 1 /\
      (amount record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (buy record) = 5 /\
      Datatypes.length (sell record) = 5 /\
      Datatypes.length (settlement record) = 1 /\
      Datatypes.length (auction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (trade_time record) ++
      encode_uint 4 (volume_int_324 record) ++
      encode_uint 8 (price record) ++
      encode_bytes 1 (concertation_type record) ++
      encode_uint 4 (trade_number record) ++
      encode_bytes 1 (price_setter record) ++
      encode_bytes 1 (operation_type record) ++
      encode_uint 8 (amount record) ++
      encode_bytes 5 (buy record) ++
      encode_bytes 5 (sell record) ++
      encode_bytes 1 (settlement record) ++
      encode_bytes 1 (auction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (volume_int_324_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (concertation_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (price_setter_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (operation_type_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (amount_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (buy_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (sell_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (settlement_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (auction_indicator_value, bytes) =>
                                                          Some ({| instrument_number := instrument_number_value; trade_time := trade_time_value; volume_int_324 := volume_int_324_value; price := price_value; concertation_type := concertation_type_value; trade_number := trade_number_value; price_setter := price_setter_value; operation_type := operation_type_value; amount := amount_value; buy := buy_value; sell := sell_value; settlement := settlement_value; auction_indicator := auction_indicator_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CapitalTradesMessage.

  Module RegistryOperationsMessage.

    (** Sent whenever there is a debt or capital instrument placement. *)
    Record t := {
      instrument_number : N;
      offer_type : list byte;
      income : list byte;
      value_type : list byte;
      issuer : list byte;
      series : list byte;
      maximum_volume : N;
      registered_volume : N;
      price_rate : N;
      settlement_date : N;
      firm : list byte;
      movement : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (offer_type record) = 1 /\
      Datatypes.length (income record) = 1 /\
      Datatypes.length (value_type record) = 4 /\
      Datatypes.length (issuer record) = 7 /\
      Datatypes.length (series record) = 6 /\
      (maximum_volume record < 256 ^ N.of_nat 8)%N /\
      (registered_volume record < 256 ^ N.of_nat 8)%N /\
      (price_rate record < 256 ^ N.of_nat 8)%N /\
      (settlement_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (firm record) = 5 /\
      Datatypes.length (movement record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (offer_type record) ++
      encode_bytes 1 (income record) ++
      encode_bytes 4 (value_type record) ++
      encode_bytes 7 (issuer record) ++
      encode_bytes 6 (series record) ++
      encode_uint 8 (maximum_volume record) ++
      encode_uint 8 (registered_volume record) ++
      encode_uint 8 (price_rate record) ++
      encode_uint 8 (settlement_date record) ++
      encode_bytes 5 (firm record) ++
      encode_bytes 1 (movement record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (offer_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (income_value, bytes) =>
                  match decode_bytes 4 bytes with
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
                              | Some (maximum_volume_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (registered_volume_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (price_rate_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (settlement_date_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (firm_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (movement_value, bytes) =>
                                                      Some ({| instrument_number := instrument_number_value; offer_type := offer_type_value; income := income_value; value_type := value_type_value; issuer := issuer_value; series := series_value; maximum_volume := maximum_volume_value; registered_volume := registered_volume_value; price_rate := price_rate_value; settlement_date := settlement_date_value; firm := firm_value; movement := movement_value |}, bytes)
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

  End RegistryOperationsMessage.

  Module PublicOfferingsMessage.

    (** Trade from a Public offering. *)
    Record t := {
      instrument_number : N;
      number : N;
      volume_int_648 : N;
      discount_rate_or_price : N;
      rate_of_return : N;
      term_days : N;
      currency_type : list byte;
      settlement : list byte;
      buy : list byte;
      sell : list byte;
      placement_date : N;
      issue_date : N;
      maturity_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (number record < 256 ^ N.of_nat 4)%N /\
      (volume_int_648 record < 256 ^ N.of_nat 8)%N /\
      (discount_rate_or_price record < 256 ^ N.of_nat 8)%N /\
      (rate_of_return record < 256 ^ N.of_nat 4)%N /\
      (term_days record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (currency_type record) = 1 /\
      Datatypes.length (settlement record) = 1 /\
      Datatypes.length (buy record) = 5 /\
      Datatypes.length (sell record) = 5 /\
      (placement_date record < 256 ^ N.of_nat 8)%N /\
      (issue_date record < 256 ^ N.of_nat 8)%N /\
      (maturity_date record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 4 (number record) ++
      encode_uint 8 (volume_int_648 record) ++
      encode_uint 8 (discount_rate_or_price record) ++
      encode_uint 4 (rate_of_return record) ++
      encode_uint 2 (term_days record) ++
      encode_bytes 1 (currency_type record) ++
      encode_bytes 1 (settlement record) ++
      encode_bytes 5 (buy record) ++
      encode_bytes 5 (sell record) ++
      encode_uint 8 (placement_date record) ++
      encode_uint 8 (issue_date record) ++
      encode_uint 8 (maturity_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (volume_int_648_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (discount_rate_or_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (rate_of_return_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (term_days_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (currency_type_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (settlement_value, bytes) =>
                                      match decode_bytes 5 bytes with
                                      | None => None
                                      | Some (buy_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (sell_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (placement_date_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (issue_date_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (maturity_date_value, bytes) =>
                                                          Some ({| instrument_number := instrument_number_value; number := number_value; volume_int_648 := volume_int_648_value; discount_rate_or_price := discount_rate_or_price_value; rate_of_return := rate_of_return_value; term_days := term_days_value; currency_type := currency_type_value; settlement := settlement_value; buy := buy_value; sell := sell_value; placement_date := placement_date_value; issue_date := issue_date_value; maturity_date := maturity_date_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 66.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PublicOfferingsMessage.

End BmvMarketDataProduct11V11.
