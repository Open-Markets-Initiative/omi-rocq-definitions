From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Bolsa Mexicana de Valores Bmv Market Data Snapshot

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
      - a run filling what frames it
      - a run counted by a field

    License: MIT No Attribution
  *)

Module BmvMarketDataSnapshotV11Tcp.

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

  Module LoginResponseMessage.

    (** Answers a login request. *)
    Record t := {
      login_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_response_status_value, bytes) =>
          Some ({| login_response_status := login_response_status_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginResponseMessage.

  Module ReplayResponseMessage.

    (** Answers a replay request; the replayed messages follow an accepted one. *)
    Record t := {
      market_data_group : N;
      first_message : N;
      quantity : N;
      replay_response_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (first_message record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (replay_response_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (market_data_group record) ++
      encode_uint 4 (first_message record) ++
      encode_uint 2 (quantity record) ++
      encode_bytes 1 (replay_response_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (market_data_group_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (first_message_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (replay_response_status_value, bytes) =>
                      Some ({| market_data_group := market_data_group_value; first_message := first_message_value; quantity := quantity_value; replay_response_status := replay_response_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End ReplayResponseMessage.

  Module SnapshotResponseMessage.

    (** Answers a snapshot request. *)
    Record t := {
      quantity_of_messages : N;
      snapshot_response_status : list byte;
      snapshot_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (quantity_of_messages record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (snapshot_response_status record) = 1 /\
      (snapshot_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (quantity_of_messages record) ++
      encode_bytes 1 (snapshot_response_status record) ++
      encode_uint 1 (snapshot_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (quantity_of_messages_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (snapshot_response_status_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (snapshot_type_value, bytes) =>
                  Some ({| quantity_of_messages := quantity_of_messages_value; snapshot_response_status := snapshot_response_status_value; snapshot_type := snapshot_type_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SnapshotResponseMessage.

  Module SnapshotCompleteMessage.

    (** Ends a snapshot with the sequence number it synchronizes with on the online channel. *)
    Record t := {
      sequence_number : N;
      market_data_group : N;
      snapshot_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (market_data_group record < 256 ^ N.of_nat 1)%N /\
      (snapshot_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 1 (market_data_group record) ++
      encode_uint 1 (snapshot_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (market_data_group_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (snapshot_type_value, bytes) =>
                  Some ({| sequence_number := sequence_number_value; market_data_group := market_data_group_value; snapshot_type := snapshot_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End SnapshotCompleteMessage.

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
      buy_alpha_5 : list byte;
      sell_alpha_5 : list byte;
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
      Datatypes.length (buy_alpha_5 record) = 5 /\
      Datatypes.length (sell_alpha_5 record) = 5 /\
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
      encode_bytes 5 (buy_alpha_5 record) ++
      encode_bytes 5 (sell_alpha_5 record) ++
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
                                          | Some (buy_alpha_5_value, bytes) =>
                                              match decode_bytes 5 bytes with
                                              | None => None
                                              | Some (sell_alpha_5_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (settlement_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (auction_indicator_value, bytes) =>
                                                          Some ({| instrument_number := instrument_number_value; trade_time := trade_time_value; volume_int_324 := volume_int_324_value; price := price_value; concertation_type := concertation_type_value; trade_number := trade_number_value; price_setter := price_setter_value; operation_type := operation_type_value; amount := amount_value; buy_alpha_5 := buy_alpha_5_value; sell_alpha_5 := sell_alpha_5_value; settlement := settlement_value; auction_indicator := auction_indicator_value |}, bytes)
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
      buy_alpha_5 : list byte;
      sell_alpha_5 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (virtual_trades_status record) = 1 /\
      Datatypes.length (operation_type record) = 1 /\
      (number record < 256 ^ N.of_nat 4)%N /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (concertation record) = 1 /\
      Datatypes.length (buy_alpha_5 record) = 5 /\
      Datatypes.length (sell_alpha_5 record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (virtual_trades_status record) ++
      encode_bytes 1 (operation_type record) ++
      encode_uint 4 (number record) ++
      encode_uint 4 (volume_int_324 record) ++
      encode_bytes 1 (concertation record) ++
      encode_bytes 5 (buy_alpha_5 record) ++
      encode_bytes 5 (sell_alpha_5 record).

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
                              | Some (buy_alpha_5_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (sell_alpha_5_value, bytes) =>
                                      Some ({| instrument_number := instrument_number_value; virtual_trades_status := virtual_trades_status_value; operation_type := operation_type_value; number := number_value; volume_int_324 := volume_int_324_value; concertation := concertation_value; buy_alpha_5 := buy_alpha_5_value; sell_alpha_5 := sell_alpha_5_value |}, bytes)
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

  Module BestOfferMessage.

    (** Message sent by instrument when best offer changes in the electronic book. *)
    Record t := {
      instrument_number : N;
      volume_int_324 : N;
      price_rate : N;
      offer_direction : list byte;
      operation_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N /\
      (price_rate record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (offer_direction record) = 1 /\
      Datatypes.length (operation_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 4 (volume_int_324 record) ++
      encode_uint 8 (price_rate record) ++
      encode_bytes 1 (offer_direction record) ++
      encode_bytes 1 (operation_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (volume_int_324_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_rate_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (offer_direction_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (operation_type_value, bytes) =>
                          Some ({| instrument_number := instrument_number_value; volume_int_324 := volume_int_324_value; price_rate := price_rate_value; offer_direction := offer_direction_value; operation_type := operation_type_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestOfferMessage.

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
      buy_alpha_5 : list byte;
      sell_alpha_5 : list byte;
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
      Datatypes.length (buy_alpha_5 record) = 5 /\
      Datatypes.length (sell_alpha_5 record) = 5 /\
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
      encode_bytes 5 (buy_alpha_5 record) ++
      encode_bytes 5 (sell_alpha_5 record) ++
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
                                      | Some (buy_alpha_5_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (sell_alpha_5_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (placement_date_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (issue_date_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (maturity_date_value, bytes) =>
                                                          Some ({| instrument_number := instrument_number_value; number := number_value; volume_int_648 := volume_int_648_value; discount_rate_or_price := discount_rate_or_price_value; rate_of_return := rate_of_return_value; term_days := term_days_value; currency_type := currency_type_value; settlement := settlement_value; buy_alpha_5 := buy_alpha_5_value; sell_alpha_5 := sell_alpha_5_value; placement_date := placement_date_value; issue_date := issue_date_value; maturity_date := maturity_date_value |}, bytes)
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

  Module OpenInterestMessage.

    (** Open Interest *)
    Record t := {
      instrument_number : N;
      open_interest : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (open_interest record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 4 (open_interest record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (open_interest_value, bytes) =>
              Some ({| instrument_number := instrument_number_value; open_interest := open_interest_value |}, bytes)
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

  End OpenInterestMessage.

  Module DerivativesMarketTradesMessage.

    (** Contains information on any MexDer accepted transaction. *)
    Record t := {
      instrument_number : N;
      trade_time : N;
      volume_int_324 : N;
      price_rate : N;
      concertation_type : list byte;
      trade_number : N;
      operation_type : list byte;
      amount : N;
      parent_trade_number : N;
      leg_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (trade_time record < 256 ^ N.of_nat 8)%N /\
      (volume_int_324 record < 256 ^ N.of_nat 4)%N /\
      (price_rate record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (concertation_type record) = 1 /\
      (trade_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (operation_type record) = 1 /\
      (amount record < 256 ^ N.of_nat 8)%N /\
      (parent_trade_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (leg_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (trade_time record) ++
      encode_uint 4 (volume_int_324 record) ++
      encode_uint 8 (price_rate record) ++
      encode_bytes 1 (concertation_type record) ++
      encode_uint 4 (trade_number record) ++
      encode_bytes 1 (operation_type record) ++
      encode_uint 8 (amount record) ++
      encode_uint 4 (parent_trade_number record) ++
      encode_bytes 1 (leg_type record).

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
                  | Some (price_rate_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (concertation_type_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (operation_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (amount_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (parent_trade_number_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (leg_type_value, bytes) =>
                                              Some ({| instrument_number := instrument_number_value; trade_time := trade_time_value; volume_int_324 := volume_int_324_value; price_rate := price_rate_value; concertation_type := concertation_type_value; trade_number := trade_number_value; operation_type := operation_type_value; amount := amount_value; parent_trade_number := parent_trade_number_value; leg_type := leg_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DerivativesMarketTradesMessage.

  Module StatisticsOfInstrumentsMessage.

    (** Update message from derivatives statistics sent each time there is an update on the trading floor at any level price. *)
    Record t := {
      instrument_number : N;
      previous_settlement_price : N;
      opening_price : N;
      max_price_of_the_day : N;
      lower_price_of_the_day : N;
      last_price_of_the_day : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (previous_settlement_price record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (max_price_of_the_day record < 256 ^ N.of_nat 8)%N /\
      (lower_price_of_the_day record < 256 ^ N.of_nat 8)%N /\
      (last_price_of_the_day record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (previous_settlement_price record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (max_price_of_the_day record) ++
      encode_uint 8 (lower_price_of_the_day record) ++
      encode_uint 8 (last_price_of_the_day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (previous_settlement_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (opening_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (max_price_of_the_day_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (lower_price_of_the_day_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (last_price_of_the_day_value, bytes) =>
                              Some ({| instrument_number := instrument_number_value; previous_settlement_price := previous_settlement_price_value; opening_price := opening_price_value; max_price_of_the_day := max_price_of_the_day_value; lower_price_of_the_day := lower_price_of_the_day_value; last_price_of_the_day := last_price_of_the_day_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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

  End StatisticsOfInstrumentsMessage.

  Module GeneralIndicesMessage.

    (** Information about the MSE Indices. *)
    Record t := {
      component : list byte;
      sector : N;
      indices_hour : N;
      volume_int_648 : N;
      indices_price_44 : N;
      variation : N;
      percentage : N;
      trend : list byte;
      indices_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (component record) = 2 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (indices_hour record < 256 ^ N.of_nat 8)%N /\
      (volume_int_648 record < 256 ^ N.of_nat 8)%N /\
      (indices_price_44 record < 256 ^ N.of_nat 4)%N /\
      (variation record < 256 ^ N.of_nat 4)%N /\
      (percentage record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trend record) = 1 /\
      Datatypes.length (indices_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (component record) ++
      encode_uint 1 (sector record) ++
      encode_uint 8 (indices_hour record) ++
      encode_uint 8 (volume_int_648 record) ++
      encode_uint 4 (indices_price_44 record) ++
      encode_uint 4 (variation record) ++
      encode_uint 4 (percentage record) ++
      encode_bytes 1 (trend record) ++
      encode_bytes 1 (indices_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (component_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (sector_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (indices_hour_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (volume_int_648_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (indices_price_44_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (variation_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (percentage_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trend_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (indices_status_value, bytes) =>
                                          Some ({| component := component_value; sector := sector_value; indices_hour := indices_hour_value; volume_int_648 := volume_int_648_value; indices_price_44 := indices_price_44_value; variation := variation_value; percentage := percentage_value; trend := trend_value; indices_status := indices_status_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GeneralIndicesMessage.

  Module IndicesComponentsMessage.

    (** Indices components obtained during the day. *)
    Record t := {
      date : N;
      component : list byte;
      sector : N;
      type : list byte;
      issuer : list byte;
      series : list byte;
      indices_stocks : N;
      last_price : N;
      closing_price : N;
      influence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (component record) = 2 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (type record) = 1 /\
      Datatypes.length (issuer record) = 7 /\
      Datatypes.length (series record) = 6 /\
      (indices_stocks record < 256 ^ N.of_nat 8)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (influence record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (date record) ++
      encode_bytes 2 (component record) ++
      encode_uint 1 (sector record) ++
      encode_bytes 1 (type record) ++
      encode_bytes 7 (issuer record) ++
      encode_bytes 6 (series record) ++
      encode_uint 8 (indices_stocks record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 8 (influence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (date_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (component_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (sector_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (type_value, bytes) =>
                      match decode_bytes 7 bytes with
                      | None => None
                      | Some (issuer_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (series_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (indices_stocks_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (last_price_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (closing_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (influence_value, bytes) =>
                                              Some ({| date := date_value; component := component_value; sector := sector_value; type := type_value; issuer := issuer_value; series := series_value; indices_stocks := indices_stocks_value; last_price := last_price_value; closing_price := closing_price_value; influence := influence_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndicesComponentsMessage.

  Module InavMessage.

    (** TRACS dissemination during continuous market trading hours. *)
    Record t := {
      trac_number : N;
      theoretical_current_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trac_number record < 256 ^ N.of_nat 4)%N /\
      (theoretical_current_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trac_number record) ++
      encode_uint 8 (theoretical_current_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (trac_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (theoretical_current_price_value, bytes) =>
              Some ({| trac_number := trac_number_value; theoretical_current_price := theoretical_current_price_value |}, bytes)
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

  End InavMessage.

  Module DollarBuySellMessage.

    (** Dollar Buy/Sell *)
    Record t := {
      posture_date : N;
      currency : list byte;
      dollar_side : list byte;
      buy_precio_88 : N;
      sell_precio_88 : N;
      last_deal : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (posture_date record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (currency record) = 5 /\
      Datatypes.length (dollar_side record) = 1 /\
      (buy_precio_88 record < 256 ^ N.of_nat 8)%N /\
      (sell_precio_88 record < 256 ^ N.of_nat 8)%N /\
      (last_deal record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (posture_date record) ++
      encode_bytes 5 (currency record) ++
      encode_bytes 1 (dollar_side record) ++
      encode_uint 8 (buy_precio_88 record) ++
      encode_uint 8 (sell_precio_88 record) ++
      encode_uint 8 (last_deal record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (posture_date_value, bytes) =>
          match decode_bytes 5 bytes with
          | None => None
          | Some (currency_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (dollar_side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (buy_precio_88_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (sell_precio_88_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (last_deal_value, bytes) =>
                              Some ({| posture_date := posture_date_value; currency := currency_value; dollar_side := dollar_side_value; buy_precio_88 := buy_precio_88_value; sell_precio_88 := sell_precio_88_value; last_deal := last_deal_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End DollarBuySellMessage.

  Module ShortSalesBalancesPerInstrumentMessage.

    (** Short sales balances per instrument *)
    Record t := {
      instrument_number : N;
      date : N;
      previous_balance : N;
      amount_traded : N;
      buybacks : N;
      current_balance : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (date record < 256 ^ N.of_nat 8)%N /\
      (previous_balance record < 256 ^ N.of_nat 8)%N /\
      (amount_traded record < 256 ^ N.of_nat 8)%N /\
      (buybacks record < 256 ^ N.of_nat 8)%N /\
      (current_balance record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (date record) ++
      encode_uint 8 (previous_balance record) ++
      encode_uint 8 (amount_traded record) ++
      encode_uint 8 (buybacks record) ++
      encode_uint 8 (current_balance record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (previous_balance_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (amount_traded_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (buybacks_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (current_balance_value, bytes) =>
                              Some ({| instrument_number := instrument_number_value; date := date_value; previous_balance := previous_balance_value; amount_traded := amount_traded_value; buybacks := buybacks_value; current_balance := current_balance_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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

  End ShortSalesBalancesPerInstrumentMessage.

  Module CapitalMarketMultiplesMessage.

    (** Capital Market Multiples *)
    Record t := {
      instrument_id : N;
      multiple_type : list byte;
      registry_number : list byte;
      sector : N;
      subsector : N;
      business_line : N;
      sub_line : N;
      pflepa_multiple : N;
      pfepa_multiple : N;
      ve_uaiida_multiple : N;
      p_u : N;
      p_vl : N;
      f_1_p_unoc : N;
      f_2_p_unoc : N;
      f_1_p_ue : N;
      f_2_p_ue : N;
      f_1_ve_uaiida : N;
      f_2_ve_uaiida : N;
      f_1_p_u : N;
      f_2_p_u : N;
      f_1_p_vl : N;
      f_2_p_vl : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (multiple_type record) = 1 /\
      Datatypes.length (registry_number record) = 1 /\
      (sector record < 256 ^ N.of_nat 1)%N /\
      (subsector record < 256 ^ N.of_nat 1)%N /\
      (business_line record < 256 ^ N.of_nat 1)%N /\
      (sub_line record < 256 ^ N.of_nat 1)%N /\
      (pflepa_multiple record < 256 ^ N.of_nat 8)%N /\
      (pfepa_multiple record < 256 ^ N.of_nat 8)%N /\
      (ve_uaiida_multiple record < 256 ^ N.of_nat 8)%N /\
      (p_u record < 256 ^ N.of_nat 8)%N /\
      (p_vl record < 256 ^ N.of_nat 8)%N /\
      (f_1_p_unoc record < 256 ^ N.of_nat 8)%N /\
      (f_2_p_unoc record < 256 ^ N.of_nat 8)%N /\
      (f_1_p_ue record < 256 ^ N.of_nat 8)%N /\
      (f_2_p_ue record < 256 ^ N.of_nat 8)%N /\
      (f_1_ve_uaiida record < 256 ^ N.of_nat 8)%N /\
      (f_2_ve_uaiida record < 256 ^ N.of_nat 8)%N /\
      (f_1_p_u record < 256 ^ N.of_nat 8)%N /\
      (f_2_p_u record < 256 ^ N.of_nat 8)%N /\
      (f_1_p_vl record < 256 ^ N.of_nat 8)%N /\
      (f_2_p_vl record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_bytes 1 (multiple_type record) ++
      encode_bytes 1 (registry_number record) ++
      encode_uint 1 (sector record) ++
      encode_uint 1 (subsector record) ++
      encode_uint 1 (business_line record) ++
      encode_uint 1 (sub_line record) ++
      encode_uint 8 (pflepa_multiple record) ++
      encode_uint 8 (pfepa_multiple record) ++
      encode_uint 8 (ve_uaiida_multiple record) ++
      encode_uint 8 (p_u record) ++
      encode_uint 8 (p_vl record) ++
      encode_uint 8 (f_1_p_unoc record) ++
      encode_uint 8 (f_2_p_unoc record) ++
      encode_uint 8 (f_1_p_ue record) ++
      encode_uint 8 (f_2_p_ue record) ++
      encode_uint 8 (f_1_ve_uaiida record) ++
      encode_uint 8 (f_2_ve_uaiida record) ++
      encode_uint 8 (f_1_p_u record) ++
      encode_uint 8 (f_2_p_u record) ++
      encode_uint 8 (f_1_p_vl record) ++
      encode_uint 8 (f_2_p_vl record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (multiple_type_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (registry_number_value, bytes) =>
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
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (pflepa_multiple_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (pfepa_multiple_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (ve_uaiida_multiple_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (p_u_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (p_vl_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (f_1_p_unoc_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (f_2_p_unoc_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (f_1_p_ue_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (f_2_p_ue_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (f_1_ve_uaiida_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (f_2_ve_uaiida_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (f_1_p_u_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (f_2_p_u_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (f_1_p_vl_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (f_2_p_vl_value, bytes) =>
                                                                                              Some ({| instrument_id := instrument_id_value; multiple_type := multiple_type_value; registry_number := registry_number_value; sector := sector_value; subsector := subsector_value; business_line := business_line_value; sub_line := sub_line_value; pflepa_multiple := pflepa_multiple_value; pfepa_multiple := pfepa_multiple_value; ve_uaiida_multiple := ve_uaiida_multiple_value; p_u := p_u_value; p_vl := p_vl_value; f_1_p_unoc := f_1_p_unoc_value; f_2_p_unoc := f_2_p_unoc_value; f_1_p_ue := f_1_p_ue_value; f_2_p_ue := f_2_p_ue_value; f_1_ve_uaiida := f_1_ve_uaiida_value; f_2_ve_uaiida := f_2_ve_uaiida_value; f_1_p_u := f_1_p_u_value; f_2_p_u := f_2_p_u_value; f_1_p_vl := f_1_p_vl_value; f_2_p_vl := f_2_p_vl_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 130.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
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

  End CapitalMarketMultiplesMessage.

  Module BenchmarkMessage.

    (** Benchmark *)
    Record t := {
      benchmark_name : list byte;
      benchmark_date : N;
      outstanding : N;
      integer_amount : N;
      decimal_amount : N;
      indices_precio_88 : N;
      indices_24 : N;
      rebalance : list byte;
      daily_performance : N;
      annual_performance : N;
      monthly_performance : N;
      last_12_months_performance : N;
      v24_hours_daily_performance : N;
      v24_hours_annual_performance : N;
      v24_hours_monthly_performance : N;
      last_12_months_24_hours_performance : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (benchmark_name record) = 40 /\
      (benchmark_date record < 256 ^ N.of_nat 8)%N /\
      (outstanding record < 256 ^ N.of_nat 8)%N /\
      (integer_amount record < 256 ^ N.of_nat 8)%N /\
      (decimal_amount record < 256 ^ N.of_nat 4)%N /\
      (indices_precio_88 record < 256 ^ N.of_nat 8)%N /\
      (indices_24 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (rebalance record) = 1 /\
      (daily_performance record < 256 ^ N.of_nat 8)%N /\
      (annual_performance record < 256 ^ N.of_nat 8)%N /\
      (monthly_performance record < 256 ^ N.of_nat 8)%N /\
      (last_12_months_performance record < 256 ^ N.of_nat 8)%N /\
      (v24_hours_daily_performance record < 256 ^ N.of_nat 8)%N /\
      (v24_hours_annual_performance record < 256 ^ N.of_nat 8)%N /\
      (v24_hours_monthly_performance record < 256 ^ N.of_nat 8)%N /\
      (last_12_months_24_hours_performance record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 40 (benchmark_name record) ++
      encode_uint 8 (benchmark_date record) ++
      encode_uint 8 (outstanding record) ++
      encode_uint 8 (integer_amount record) ++
      encode_uint 4 (decimal_amount record) ++
      encode_uint 8 (indices_precio_88 record) ++
      encode_uint 8 (indices_24 record) ++
      encode_bytes 1 (rebalance record) ++
      encode_uint 8 (daily_performance record) ++
      encode_uint 8 (annual_performance record) ++
      encode_uint 8 (monthly_performance record) ++
      encode_uint 8 (last_12_months_performance record) ++
      encode_uint 8 (v24_hours_daily_performance record) ++
      encode_uint 8 (v24_hours_annual_performance record) ++
      encode_uint 8 (v24_hours_monthly_performance record) ++
      encode_uint 8 (last_12_months_24_hours_performance record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 40 bytes with
      | None => None
      | Some (benchmark_name_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (benchmark_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (outstanding_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (integer_amount_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (decimal_amount_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (indices_precio_88_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (indices_24_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (rebalance_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (daily_performance_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (annual_performance_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (monthly_performance_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (last_12_months_performance_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (v24_hours_daily_performance_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (v24_hours_annual_performance_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (v24_hours_monthly_performance_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (last_12_months_24_hours_performance_value, bytes) =>
                                                                      Some ({| benchmark_name := benchmark_name_value; benchmark_date := benchmark_date_value; outstanding := outstanding_value; integer_amount := integer_amount_value; decimal_amount := decimal_amount_value; indices_precio_88 := indices_precio_88_value; indices_24 := indices_24_value; rebalance := rebalance_value; daily_performance := daily_performance_value; annual_performance := annual_performance_value; monthly_performance := monthly_performance_value; last_12_months_performance := last_12_months_performance_value; v24_hours_daily_performance := v24_hours_daily_performance_value; v24_hours_annual_performance := v24_hours_annual_performance_value; v24_hours_monthly_performance := v24_hours_monthly_performance_value; last_12_months_24_hours_performance := last_12_months_24_hours_performance_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 149.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
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
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BenchmarkMessage.

  Module CapitalizationRulesMessage.

    (** Capitalization Rules *)
    Record t := {
      instrument_number : N;
      date_indicators : N;
      bursatility_indices : N;
      bursatility_indices_sign : list byte;
      beta_coefficient : N;
      beta_coefficient_sign : list byte;
      correlation_coefficient : N;
      correlation_coefficient_sign : list byte;
      delta_difference : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (date_indicators record < 256 ^ N.of_nat 8)%N /\
      (bursatility_indices record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (bursatility_indices_sign record) = 1 /\
      (beta_coefficient record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (beta_coefficient_sign record) = 1 /\
      (correlation_coefficient record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (correlation_coefficient_sign record) = 1 /\
      (delta_difference record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (date_indicators record) ++
      encode_uint 4 (bursatility_indices record) ++
      encode_bytes 1 (bursatility_indices_sign record) ++
      encode_uint 8 (beta_coefficient record) ++
      encode_bytes 1 (beta_coefficient_sign record) ++
      encode_uint 8 (correlation_coefficient record) ++
      encode_bytes 1 (correlation_coefficient_sign record) ++
      encode_uint 4 (delta_difference record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (date_indicators_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (bursatility_indices_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (bursatility_indices_sign_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (beta_coefficient_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (beta_coefficient_sign_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (correlation_coefficient_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (correlation_coefficient_sign_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (delta_difference_value, bytes) =>
                                          Some ({| instrument_number := instrument_number_value; date_indicators := date_indicators_value; bursatility_indices := bursatility_indices_value; bursatility_indices_sign := bursatility_indices_sign_value; beta_coefficient := beta_coefficient_value; beta_coefficient_sign := beta_coefficient_sign_value; correlation_coefficient := correlation_coefficient_value; correlation_coefficient_sign := correlation_coefficient_sign_value; delta_difference := delta_difference_value |}, bytes)
                                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CapitalizationRulesMessage.

  Module ClosingPriceOriginMessage.

    (** Closing price origin *)
    Record t := {
      instrument_number : N;
      origin_price : N;
      sending : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      (origin_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (sending record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_uint 8 (origin_price record) ++
      encode_bytes 1 (sending record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (origin_price_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (sending_value, bytes) =>
                  Some ({| instrument_number := instrument_number_value; origin_price := origin_price_value; sending := sending_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClosingPriceOriginMessage.

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
      subsector : N;
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
      (subsector record < 256 ^ N.of_nat 1)%N /\
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
      encode_uint 1 (subsector record) ++
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
                              | Some (subsector_value, bytes) =>
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
                                                                  Some ({| number_of_the_instrument := number_of_the_instrument_value; origin := origin_value; type_of_value := type_of_value_value; issuing_company := issuing_company_value; series := series_value; sector := sector_value; subsector := subsector_value; industry := industry_value; sub_industry := sub_industry_value; trading_company := trading_company_value; reference_price := reference_price_value; reference_date := reference_date_value; reference := reference_value; isin := isin_value; rating := rating_value |}, bytes)
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
      volume_int_648 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (probable_price_of_allocation record < 256 ^ N.of_nat 8)%N /\
      (volume_int_648 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (probable_price_of_allocation record) ++
      encode_uint 8 (volume_int_648 record).

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
                  | Some (volume_int_648_value, bytes) =>
                      Some ({| instrument_number := instrument_number_value; origin := origin_value; probable_price_of_allocation := probable_price_of_allocation_value; volume_int_648 := volume_int_648_value |}, bytes)
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
      volume_int_648 : N;
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
      (volume_int_648 record < 256 ^ N.of_nat 8)%N /\
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
      encode_uint 8 (volume_int_648 record) ++
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
                  | Some (volume_int_648_value, bytes) =>
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
                                                                  Some ({| instrument_number := instrument_number_value; origin := origin_value; time_of_the_trade := time_of_the_trade_value; volume_int_648 := volume_int_648_value; price := price_value; type_of_agreement := type_of_agreement_value; consecutive_number_of_the_trade := consecutive_number_of_the_trade_value; sets_price := sets_price_value; type_of_trading := type_of_trading_value; amount := amount_value; purchases := purchases_value; sells := sells_value; settlement := settlement_value; auction_indicator := auction_indicator_value; indicator := indicator_value |}, bytes)
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

  Module PricevolumeIndicatorMessage.

    (** Price/volume indicator for the messages coming from BIVA. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      probable_price_of_allotment : N;
      volume_int_648 : N;
      best_selling_price : N;
      best_purchasing_price : N;
      type_of_cross_trading : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (probable_price_of_allotment record < 256 ^ N.of_nat 8)%N /\
      (volume_int_648 record < 256 ^ N.of_nat 8)%N /\
      (best_selling_price record < 256 ^ N.of_nat 8)%N /\
      (best_purchasing_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (type_of_cross_trading record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (probable_price_of_allotment record) ++
      encode_uint 8 (volume_int_648 record) ++
      encode_uint 8 (best_selling_price record) ++
      encode_uint 8 (best_purchasing_price record) ++
      encode_bytes 1 (type_of_cross_trading record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (probable_price_of_allotment_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (volume_int_648_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (best_selling_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (best_purchasing_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (type_of_cross_trading_value, bytes) =>
                                  Some ({| instrument_number := instrument_number_value; origin := origin_value; probable_price_of_allotment := probable_price_of_allotment_value; volume_int_648 := volume_int_648_value; best_selling_price := best_selling_price_value; best_purchasing_price := best_purchasing_price_value; type_of_cross_trading := type_of_cross_trading_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PricevolumeIndicatorMessage.

  Module ConsolidatedExecutionOfOrdersMessage.

    (** The message is published when there is a term matching or closing in the electronic system of the BMV or BIVA. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      date : N;
      consecutive_number : N;
      volume_int_648 : N;
      consecutive_number_of_the_trade : N;
      execution_price : N;
      indicator : list byte;
      sets_price : list byte;
      participant : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (date record < 256 ^ N.of_nat 8)%N /\
      (consecutive_number record < 256 ^ N.of_nat 8)%N /\
      (volume_int_648 record < 256 ^ N.of_nat 8)%N /\
      (consecutive_number_of_the_trade record < 256 ^ N.of_nat 8)%N /\
      (execution_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (indicator record) = 1 /\
      Datatypes.length (sets_price record) = 1 /\
      Datatypes.length (participant record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (date record) ++
      encode_uint 8 (consecutive_number record) ++
      encode_uint 8 (volume_int_648 record) ++
      encode_uint 8 (consecutive_number_of_the_trade record) ++
      encode_uint 8 (execution_price record) ++
      encode_bytes 1 (indicator record) ++
      encode_bytes 1 (sets_price record) ++
      encode_bytes 5 (participant record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (date_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consecutive_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (volume_int_648_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (consecutive_number_of_the_trade_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (execution_price_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (indicator_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (sets_price_value, bytes) =>
                                          match decode_bytes 5 bytes with
                                          | None => None
                                          | Some (participant_value, bytes) =>
                                              Some ({| instrument_number := instrument_number_value; origin := origin_value; date := date_value; consecutive_number := consecutive_number_value; volume_int_648 := volume_int_648_value; consecutive_number_of_the_trade := consecutive_number_of_the_trade_value; execution_price := execution_price_value; indicator := indicator_value; sets_price := sets_price_value; participant := participant_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConsolidatedExecutionOfOrdersMessage.

  Module RegistrationOfOrderMessage.

    (** When the order is accepted by the central system of the BMV or BIVA, this message is sent to the appropriate media. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      date_and_time : N;
      consecutive_number : N;
      direction : list byte;
      volume_int_648 : N;
      price : N;
      participant : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (date_and_time record < 256 ^ N.of_nat 8)%N /\
      (consecutive_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (direction record) = 1 /\
      (volume_int_648 record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (participant record) = 5.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (date_and_time record) ++
      encode_uint 8 (consecutive_number record) ++
      encode_bytes 1 (direction record) ++
      encode_uint 8 (volume_int_648 record) ++
      encode_uint 8 (price record) ++
      encode_bytes 5 (participant record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (date_and_time_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consecutive_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (direction_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (volume_int_648_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (price_value, bytes) =>
                                  match decode_bytes 5 bytes with
                                  | None => None
                                  | Some (participant_value, bytes) =>
                                      Some ({| instrument_number := instrument_number_value; origin := origin_value; date_and_time := date_and_time_value; consecutive_number := consecutive_number_value; direction := direction_value; volume_int_648 := volume_int_648_value; price := price_value; participant := participant_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegistrationOfOrderMessage.

  Module CancellationsOfOrdersMessage.

    (** This message deletes the trading floor order. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      date : N;
      consecutive_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (date record < 256 ^ N.of_nat 8)%N /\
      (consecutive_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (date record) ++
      encode_uint 8 (consecutive_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_number_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (origin_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (date_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consecutive_number_value, bytes) =>
                      Some ({| instrument_number := instrument_number_value; origin := origin_value; date := date_value; consecutive_number := consecutive_number_value |}, bytes)
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

  End CancellationsOfOrdersMessage.

  Module LastQuoteMessage.

    (** Message sent by instrument when the best bid is modified in the electronic book by the Origin Exchange; denotes the side that is modified, the sale or the purchase. *)
    Record t := {
      instrument_number : N;
      origin : list byte;
      volume_int_648 : N;
      price_rate : N;
      direction_of_the_bid : list byte;
      type_of_trading : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_number record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (origin record) = 1 /\
      (volume_int_648 record < 256 ^ N.of_nat 8)%N /\
      (price_rate record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (direction_of_the_bid record) = 1 /\
      Datatypes.length (type_of_trading record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_number record) ++
      encode_bytes 1 (origin record) ++
      encode_uint 8 (volume_int_648 record) ++
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
              | Some (volume_int_648_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_rate_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (direction_of_the_bid_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (type_of_trading_value, bytes) =>
                              Some ({| instrument_number := instrument_number_value; origin := origin_value; volume_int_648 := volume_int_648_value; price_rate := price_rate_value; direction_of_the_bid := direction_of_the_bid_value; type_of_trading := type_of_trading_value |}, bytes)
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

End BmvMarketDataSnapshotV11Tcp.
