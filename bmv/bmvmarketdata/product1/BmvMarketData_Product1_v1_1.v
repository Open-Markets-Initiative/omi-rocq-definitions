From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Product 1

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

Module BmvMarketDataProduct1V11.

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

  Module StatusChangesMessage.

    (** All instruments are in a certain status before and during trading session. *)
    Record t := {
      instrument_number : N;
      instrument_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (instrument_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (instrument_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (instrument_status_value, bytes) =>
              Some ({| instrument_number := instrument_number_value; instrument_status := instrument_status_value |}, bytes)
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

  End StatusChangesMessage.

  Module WeightedAveragePriceSettlementPricesMessage.

    (** For equities market, this message will be sent for each operation containing weighted average price per instrument generated within WAP calculation period (last 20 minutes of trading). *)
    Record t := {
      instrument_number : N;
      weighted_average_price : N;
      volatility : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (weighted_average_price record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (weighted_average_price record) ++
      encode_uint 8 (volatility record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (weighted_average_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (volatility_value, bytes) =>
                  Some ({| instrument_number := instrument_number_value; weighted_average_price := weighted_average_price_value; volatility := volatility_value |}, bytes)
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

  End WeightedAveragePriceSettlementPricesMessage.

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

  Module ProbableAllocationPriceMessage.

    (** Sent during any auction type (Opening, Continuous, Volatility and Intraday) and only on instruments where there is already a virtual match or pre-allocation. *)
    Record t := {
      instrument_number : N;
      probable_allocation_price : N;
      volume_int_324 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (probable_allocation_price record < 256 ^ N.of_nat 8)%N /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (probable_allocation_price record) ++
      encode_uint 4 (volume_int_324 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (probable_allocation_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (volume_int_324_value, bytes) =>
                  Some ({| instrument_number := instrument_number_value; probable_allocation_price := probable_allocation_price_value; volume_int_324 := volume_int_324_value |}, bytes)
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

  End ProbableAllocationPriceMessage.

  Module ContinuousAuctionsBeginningMessage.

    (** Sent at the moment one of the Continuous, Volatility or SIC auctions is generated. *)
    Record t := {
      instrument_number : N;
      beginning_time_of_auction : N;
      end_auction_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (beginning_time_of_auction record < 256 ^ N.of_nat 8)%N /\
      (end_auction_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (beginning_time_of_auction record) ++
      encode_uint 8 (end_auction_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (beginning_time_of_auction_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (end_auction_time_value, bytes) =>
                  Some ({| instrument_number := instrument_number_value; beginning_time_of_auction := beginning_time_of_auction_value; end_auction_time := end_auction_time_value |}, bytes)
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

  End ContinuousAuctionsBeginningMessage.

  Module MiddlePriceExistingQuotesMessage.

    (** Generated when an instrument enters a posture in the hidden electronic Middle Price book. *)
    Record t := {
      instrument_number : N;
      existing_postures : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (existing_postures record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (existing_postures record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (existing_postures_value, bytes) =>
              Some ({| instrument_number := instrument_number_value; existing_postures := existing_postures_value |}, bytes)
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

  End MiddlePriceExistingQuotesMessage.

  Module MutualFundTradesMessage.

    (** Contains any mutual funds operation realized. *)
    Record t := {
      instrument_number : N;
      trade_date : N;
      price : N;
      book_value : N;
      number_of_sales_transactions : N;
      sales_volume : N;
      number_of_buy_transactions : N;
      buy_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (book_value record < 256 ^ N.of_nat 8)%N /\
      (number_of_sales_transactions record < 256 ^ N.of_nat 4)%N /\
      (sales_volume record < 256 ^ N.of_nat 8)%N /\
      (number_of_buy_transactions record < 256 ^ N.of_nat 4)%N /\
      (buy_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (trade_date record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (book_value record) ++
      encode_uint 4 (number_of_sales_transactions record) ++
      encode_uint 8 (sales_volume record) ++
      encode_uint 4 (number_of_buy_transactions record) ++
      encode_uint 8 (buy_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (trade_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (book_value_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (number_of_sales_transactions_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (sales_volume_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (number_of_buy_transactions_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (buy_volume_value, bytes) =>
                                      Some ({| instrument_number := instrument_number_value; trade_date := trade_date_value; price := price_value; book_value := book_value_value; number_of_sales_transactions := number_of_sales_transactions_value; sales_volume := sales_volume_value; number_of_buy_transactions := number_of_buy_transactions_value; buy_volume := buy_volume_value |}, bytes)
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

  End MutualFundTradesMessage.

  Module TradabilityMessage.

    (** Message sent every half hour during trading session, informing general tradability by instrument. *)
    Record t := {
      instrument_number : N;
      number_of_operations : N;
      volume_int_648 : N;
      amount : N;
      opening_price : N;
      maximum : N;
      minimum : N;
      average : N;
      last : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (number_of_operations record < 256 ^ N.of_nat 4)%N /\
      (volume_int_648 record < 256 ^ N.of_nat 8)%N /\
      (amount record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (maximum record < 256 ^ N.of_nat 8)%N /\
      (minimum record < 256 ^ N.of_nat 8)%N /\
      (average record < 256 ^ N.of_nat 8)%N /\
      (last record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 4 (number_of_operations record) ++
      encode_uint 8 (volume_int_648 record) ++
      encode_uint 8 (amount record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (maximum record) ++
      encode_uint 8 (minimum record) ++
      encode_uint 8 (average record) ++
      encode_uint 8 (last record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (number_of_operations_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (volume_int_648_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (amount_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (opening_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (maximum_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (minimum_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (average_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (last_value, bytes) =>
                                          Some ({| instrument_number := instrument_number_value; number_of_operations := number_of_operations_value; volume_int_648 := volume_int_648_value; amount := amount_value; opening_price := opening_price_value; maximum := maximum_value; minimum := minimum_value; average := average_value; last := last_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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

  End TradabilityMessage.

  Module VirtualTradesMessage.

    (** When an operation has been pre-assigned to the at closing and average day Price electronic books, a virtual trade message is sent, where also notifying of this operation. *)
    Record t := {
      instrument_number : N;
      virtual_trades_status : list byte;
      operation_type : list byte;
      number : N;
      volume_int_324 : N;
      concertation : list byte;
      buy : list byte;
      sell : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (virtual_trades_status record) = 1 /\
      Datatypes.length (operation_type record) = 1 /\
      (number record < 256 ^ N.of_nat 4)%N /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (concertation record) = 1 /\
      Datatypes.length (buy record) = 5 /\
      Datatypes.length (sell record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (virtual_trades_status record) ++
      encode_bytes 1 (operation_type record) ++
      encode_uint 4 (number record) ++
      encode_uint 4 (volume_int_324 record) ++
      encode_bytes 1 (concertation record) ++
      encode_bytes 5 (buy record) ++
      encode_bytes 5 (sell record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (virtual_trades_status_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (operation_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (volume_int_324_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (concertation_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (buy_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (sell_value, bytes) =>
                                      Some ({| instrument_number := instrument_number_value; virtual_trades_status := virtual_trades_status_value; operation_type := operation_type_value; number := number_value; volume_int_324 := volume_int_324_value; concertation := concertation_value; buy := buy_value; sell := sell_value |}, bytes)
                                  end
                              end
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End VirtualTradesMessage.

  Module OrderAdditionMessage.

    (** The moment an order is being accepted by the BMV central system; this message is diffused to the corresponding media. *)
    Record t := {
      instrument_number : N;
      date_and_time : N;
      number : N;
      direction : list byte;
      volume_int_324 : N;
      price : N;
      participant : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (date_and_time record < 256 ^ N.of_nat 8)%N /\
      (number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (direction record) = 1 /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (participant record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (date_and_time record) ++
      encode_uint 4 (number record) ++
      encode_bytes 1 (direction record) ++
      encode_uint 4 (volume_int_324 record) ++
      encode_uint 8 (price record) ++
      encode_bytes 5 (participant record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_and_time_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (direction_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (volume_int_324_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 5 bytes with
                              | None => None
                              | Some (participant_value, bytes) =>
                                  Some ({| instrument_number := instrument_number_value; date_and_time := date_and_time_value; number := number_value; direction := direction_value; volume_int_324 := volume_int_324_value; price := price_value; participant := participant_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderAdditionMessage.

  Module ExecutionOfOrdersMessage.

    (** The message is disseminated at the time there is a matching or closing in BMV’s electronic system. *)
    Record t := {
      instrument_number : N;
      date : N;
      number : N;
      volume_int_324 : N;
      trade_number : N;
      execution_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (date record < 256 ^ N.of_nat 8)%N /\
      (number record < 256 ^ N.of_nat 4)%N /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (date record) ++
      encode_uint 4 (number record) ++
      encode_uint 4 (volume_int_324 record) ++
      encode_uint 4 (trade_number record) ++
      encode_uint 8 (execution_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (number_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (volume_int_324_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_number_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (execution_price_value, bytes) =>
                              Some ({| instrument_number := instrument_number_value; date := date_value; number := number_value; volume_int_324 := volume_int_324_value; trade_number := trade_number_value; execution_price := execution_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End ExecutionOfOrdersMessage.

  Module OrderCancellationMessage.

    (** This message fully eliminates the order from the trading floor. *)
    Record t := {
      instrument_number : N;
      date : N;
      number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (date record < 256 ^ N.of_nat 8)%N /\
      (number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (date record) ++
      encode_uint 4 (number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (number_value, bytes) =>
                  Some ({| instrument_number := instrument_number_value; date := date_value; number := number_value |}, bytes)
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

  End OrderCancellationMessage.

  Module OrderChangeMessage.

    (** Message sent when the order changes one of its data, the system allocates to it a new priority in the electronic book, the order to be replaced is identified with the original Instrument, Date and Number, the new allocation of priority in the electronic book appears in the New Date and Number fields. *)
    Record t := {
      instrument_number : N;
      original_date : N;
      original_number : N;
      new_date : N;
      new_number : N;
      direction : list byte;
      volume_int_324 : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (original_date record < 256 ^ N.of_nat 8)%N /\
      (original_number record < 256 ^ N.of_nat 4)%N /\
      (new_date record < 256 ^ N.of_nat 8)%N /\
      (new_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (direction record) = 1 /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (original_date record) ++
      encode_uint 4 (original_number record) ++
      encode_uint 8 (new_date record) ++
      encode_uint 4 (new_number record) ++
      encode_bytes 1 (direction record) ++
      encode_uint 4 (volume_int_324 record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (original_date_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (original_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (new_date_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (new_number_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (direction_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_int_324_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      Some ({| instrument_number := instrument_number_value; original_date := original_date_value; original_number := original_number_value; new_date := new_date_value; new_number := new_number_value; direction := direction_value; volume_int_324 := volume_int_324_value; price := price_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 41.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderChangeMessage.

End BmvMarketDataProduct1V11.
