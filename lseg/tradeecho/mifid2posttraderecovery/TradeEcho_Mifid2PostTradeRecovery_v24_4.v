From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * London Stock Exchange MiFID II Post Trade Recovery

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
      - a field read in bits
  *)

Module TradeEchoMifid2PostTradeRecoveryV244.

  Module UnitHeader.

    (** Gtp Tcp Unit Header *)
    Record t := {
      length_ : N;
      message_count : N;
      market_data_group : list byte;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_data_group record) = 1 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_bytes 1 (market_data_group record) ++
      encode_uint 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_data_group_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; market_data_group := market_data_group_value; sequence_number := sequence_number_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnitHeader.

  Module MessageHeader.

    (** Gtp Tcp Message Header *)
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

  Module LoginRequestMessage.

    (** Used by the client to log in to the replay or recovery channel. *)
    Record t := {
      username : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (username record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (username_value, bytes) =>
          Some ({| username := username_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End LoginRequestMessage.

  Module RecoveryRequestMessage.

    (** Used by the client to request data on the recovery channel. *)
    Record t := {
      request_level : N;
      instrument : N;
      group_id : list byte;
      request_order_book_type : N;
      source_venue : N;
      recovery_type : N;
      sequence_number : N;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_level record < 256 ^ N.of_nat 1)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (group_id record) = 6 /\
      (request_order_book_type record < 256 ^ N.of_nat 1)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (recovery_type record < 256 ^ N.of_nat 1)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (request_level record) ++
      encode_uint 8 (instrument record) ++
      encode_bytes 6 (group_id record) ++
      encode_uint 1 (request_order_book_type record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 1 (recovery_type record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (request_level_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (group_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (request_order_book_type_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (source_venue_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (recovery_type_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (sequence_number_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (request_id_value, bytes) =>
                                      Some ({| request_level := request_level_value; instrument := instrument_value; group_id := group_id_value; request_order_book_type := request_order_book_type_value; source_venue := source_venue_value; recovery_type := recovery_type_value; sequence_number := sequence_number_value; request_id := request_id_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RecoveryRequestMessage.

  Module LoginResponseMessage.

    (** Used by the server to accept or reject a login request to the replay or recovery channel. *)
    Record t := {
      login_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (login_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (login_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (login_status_value, bytes) =>
          Some ({| login_status := login_status_value |}, bytes)
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

  Module RecoveryResponseMessage.

    (** Used by the server to respond to a snapshot request on the recovery channel. *)
    Record t := {
      sequence_number : N;
      count : N;
      recovery_status : list byte;
      request_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (count record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (recovery_status record) = 1 /\
      (request_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (sequence_number record) ++
      encode_uint 4 (count record) ++
      encode_bytes 1 (recovery_status record) ++
      encode_uint 4 (request_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (recovery_status_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (request_id_value, bytes) =>
                      Some ({| sequence_number := sequence_number_value; count := count_value; recovery_status := recovery_status_value; request_id := request_id_value |}, bytes)
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RecoveryResponseMessage.

  Module ReplayAndRecoveryCompleteMessage.

    (** Used by the server to indicate the successful completion of servicing a message replay or a recovery request. *)
    Record t := {
      request_id : N;
      trading_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (request_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (request_id record) ++
      encode_bytes 1 (trading_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (request_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trading_status_value, bytes) =>
              Some ({| request_id := request_id_value; trading_status := trading_status_value |}, bytes)
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

  End ReplayAndRecoveryCompleteMessage.

  Module SystemEventMessage.

    (** Session transition is advertised via one system event message for all instruments allocated to the same multicast channel *)
    Record t := {
      timestamp : N;
      event_code : list byte;
      source_venue : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1 /\
      (source_venue record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 2 (source_venue record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  Some ({| timestamp := timestamp_value; event_code := event_code_value; source_venue := source_venue_value |}, bytes)
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

  End SystemEventMessage.

  Module InstrumentStatusMessage.

    (** A specific instrument be subject to individual status change *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      trading_status : list byte;
      session_change_reason : N;
      new_end_time : list byte;
      order_book_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (trading_status record) = 1 /\
      (session_change_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (new_end_time record) = 6 /\
      (order_book_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_bytes 1 (trading_status record) ++
      encode_uint 1 (session_change_reason record) ++
      encode_bytes 6 (new_end_time record) ++
      encode_uint 1 (order_book_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (session_change_reason_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (new_end_time_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (order_book_type_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; trading_status := trading_status_value; session_change_reason := session_change_reason_value; new_end_time := new_end_time_value; order_book_type := order_book_type_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentStatusMessage.

  Module StatisticsSnapshotMessage.

    (** A snapshot of an instrument's statistics that is used for recovery *)
    Record t := {
      timestamp : N;
      instrument : N;
      source_venue : N;
      volume : N;
      volume_on_book_only : N;
      vwap : N;
      vwap_on_book_only : N;
      number_of_trades : N;
      number_of_trades_on_book_only : N;
      turnover : N;
      turnover_on_book_only : N;
      official_opening_price : N;
      official_closing_price : N;
      trade_high_on_book_only : N;
      trade_low_on_book_only : N;
      trade_high : N;
      trade_low : N;
      fifty_two_week_trade_high : N;
      fifty_two_week_trade_low : N;
      opening_price_indicator : list byte;
      closing_price_indicator : list byte;
      iau_price : N;
      iau_paired_size : N;
      imbalance_quantity : N;
      imbalance_direction : list byte;
      best_closing_bid_price : N;
      best_closing_ask_price : N;
      best_closing_bid_size : N;
      best_closing_ask_size : N;
      trade_high_off_book : N;
      trade_low_off_book : N;
      reserved_8 : N;
      second_reserved_8 : N;
      auction_type : list byte;
      last_trade_price : N;
      last_trade_quantity : N;
      last_trade_time : N;
      static_reference_price : N;
      dynamic_reference_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      (volume record < 256 ^ N.of_nat 8)%N /\
      (volume_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (vwap_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (number_of_trades record < 256 ^ N.of_nat 4)%N /\
      (number_of_trades_on_book_only record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N /\
      (turnover_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (official_opening_price record < 256 ^ N.of_nat 8)%N /\
      (official_closing_price record < 256 ^ N.of_nat 8)%N /\
      (trade_high_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (trade_low_on_book_only record < 256 ^ N.of_nat 8)%N /\
      (trade_high record < 256 ^ N.of_nat 8)%N /\
      (trade_low record < 256 ^ N.of_nat 8)%N /\
      (fifty_two_week_trade_high record < 256 ^ N.of_nat 8)%N /\
      (fifty_two_week_trade_low record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (opening_price_indicator record) = 1 /\
      Datatypes.length (closing_price_indicator record) = 1 /\
      (iau_price record < 256 ^ N.of_nat 8)%N /\
      (iau_paired_size record < 256 ^ N.of_nat 8)%N /\
      (imbalance_quantity record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (imbalance_direction record) = 1 /\
      (best_closing_bid_price record < 256 ^ N.of_nat 8)%N /\
      (best_closing_ask_price record < 256 ^ N.of_nat 8)%N /\
      (best_closing_bid_size record < 256 ^ N.of_nat 8)%N /\
      (best_closing_ask_size record < 256 ^ N.of_nat 8)%N /\
      (trade_high_off_book record < 256 ^ N.of_nat 8)%N /\
      (trade_low_off_book record < 256 ^ N.of_nat 8)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      (second_reserved_8 record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (last_trade_price record < 256 ^ N.of_nat 8)%N /\
      (last_trade_quantity record < 256 ^ N.of_nat 8)%N /\
      (last_trade_time record < 256 ^ N.of_nat 8)%N /\
      (static_reference_price record < 256 ^ N.of_nat 8)%N /\
      (dynamic_reference_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_uint 2 (source_venue record) ++
      encode_uint 8 (volume record) ++
      encode_uint 8 (volume_on_book_only record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (vwap_on_book_only record) ++
      encode_uint 4 (number_of_trades record) ++
      encode_uint 4 (number_of_trades_on_book_only record) ++
      encode_uint 8 (turnover record) ++
      encode_uint 8 (turnover_on_book_only record) ++
      encode_uint 8 (official_opening_price record) ++
      encode_uint 8 (official_closing_price record) ++
      encode_uint 8 (trade_high_on_book_only record) ++
      encode_uint 8 (trade_low_on_book_only record) ++
      encode_uint 8 (trade_high record) ++
      encode_uint 8 (trade_low record) ++
      encode_uint 8 (fifty_two_week_trade_high record) ++
      encode_uint 8 (fifty_two_week_trade_low record) ++
      encode_bytes 1 (opening_price_indicator record) ++
      encode_bytes 1 (closing_price_indicator record) ++
      encode_uint 8 (iau_price record) ++
      encode_uint 8 (iau_paired_size record) ++
      encode_uint 8 (imbalance_quantity record) ++
      encode_bytes 1 (imbalance_direction record) ++
      encode_uint 8 (best_closing_bid_price record) ++
      encode_uint 8 (best_closing_ask_price record) ++
      encode_uint 8 (best_closing_bid_size record) ++
      encode_uint 8 (best_closing_ask_size record) ++
      encode_uint 8 (trade_high_off_book record) ++
      encode_uint 8 (trade_low_off_book record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_uint 8 (second_reserved_8 record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (last_trade_price record) ++
      encode_uint 8 (last_trade_quantity record) ++
      encode_uint 8 (last_trade_time record) ++
      encode_uint 8 (static_reference_price record) ++
      encode_uint 8 (dynamic_reference_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (source_venue_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (volume_on_book_only_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (vwap_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (vwap_on_book_only_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (number_of_trades_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (number_of_trades_on_book_only_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (turnover_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (turnover_on_book_only_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (official_opening_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (official_closing_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (trade_high_on_book_only_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (trade_low_on_book_only_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (trade_high_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (trade_low_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (fifty_two_week_trade_high_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (fifty_two_week_trade_low_value, bytes) =>
                                                                                  match decode_bytes 1 bytes with
                                                                                  | None => None
                                                                                  | Some (opening_price_indicator_value, bytes) =>
                                                                                      match decode_bytes 1 bytes with
                                                                                      | None => None
                                                                                      | Some (closing_price_indicator_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (iau_price_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (iau_paired_size_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (imbalance_quantity_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (imbalance_direction_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (best_closing_bid_price_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (best_closing_ask_price_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (best_closing_bid_size_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (best_closing_ask_size_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (trade_high_off_book_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (trade_low_off_book_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (reserved_8_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (second_reserved_8_value, bytes) =>
                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (auction_type_value, bytes) =>
                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (last_trade_price_value, bytes) =>
                                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (last_trade_quantity_value, bytes) =>
                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (last_trade_time_value, bytes) =>
                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (static_reference_price_value, bytes) =>
                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (dynamic_reference_price_value, bytes) =>
                                                                                                                                                                  Some ({| timestamp := timestamp_value; instrument := instrument_value; source_venue := source_venue_value; volume := volume_value; volume_on_book_only := volume_on_book_only_value; vwap := vwap_value; vwap_on_book_only := vwap_on_book_only_value; number_of_trades := number_of_trades_value; number_of_trades_on_book_only := number_of_trades_on_book_only_value; turnover := turnover_value; turnover_on_book_only := turnover_on_book_only_value; official_opening_price := official_opening_price_value; official_closing_price := official_closing_price_value; trade_high_on_book_only := trade_high_on_book_only_value; trade_low_on_book_only := trade_low_on_book_only_value; trade_high := trade_high_value; trade_low := trade_low_value; fifty_two_week_trade_high := fifty_two_week_trade_high_value; fifty_two_week_trade_low := fifty_two_week_trade_low_value; opening_price_indicator := opening_price_indicator_value; closing_price_indicator := closing_price_indicator_value; iau_price := iau_price_value; iau_paired_size := iau_paired_size_value; imbalance_quantity := imbalance_quantity_value; imbalance_direction := imbalance_direction_value; best_closing_bid_price := best_closing_bid_price_value; best_closing_ask_price := best_closing_ask_price_value; best_closing_bid_size := best_closing_bid_size_value; best_closing_ask_size := best_closing_ask_size_value; trade_high_off_book := trade_high_off_book_value; trade_low_off_book := trade_low_off_book_value; reserved_8 := reserved_8_value; second_reserved_8 := second_reserved_8_value; auction_type := auction_type_value; last_trade_price := last_trade_price_value; last_trade_quantity := last_trade_quantity_value; last_trade_time := last_trade_time_value; static_reference_price := static_reference_price_value; dynamic_reference_price := dynamic_reference_price_value |}, bytes)
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 270.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 bound_38]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_uint by exact bound_38.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StatisticsSnapshotMessage.

  Module MifidIiTradeReportMessage.

    (** Sent to report the MiFID compliant details of a privately negotiated trade *)
    Record t := {
      timestamp : N;
      instrument : N;
      transaction_identification_code : list byte;
      total_number_of_transactions : N;
      reserved_8 : N;
      source_venue : N;
      mi_fid_price : list byte;
      mi_fid_quantity : list byte;
      mi_fid_trading_date_and_time : list byte;
      instrument_identification_code_type : list byte;
      instrument_identification_code : list byte;
      price_notation : list byte;
      price_currency : list byte;
      notional_amount : list byte;
      notional_currency : list byte;
      venue_of_execution : list byte;
      publication_date_and_time : list byte;
      benchmark_transaction_flag : list byte;
      agency_cross_trade_flag : list byte;
      non_price_forming_transactions_flag : list byte;
      non_price_contribution_to_discovery : list byte;
      special_dividend_flag : list byte;
      pt_deferral_reason_flag : list byte;
      reference_price_transaction_flag : list byte;
      nt_liquidity_flag : list byte;
      nt_price_conditions_flag : list byte;
      algo_transaction_flag : list byte;
      pt_illiquid_flag : list byte;
      price_improvement_flag : list byte;
      cancellation_flag : list byte;
      amendment_flag : list byte;
      duplicate_flag : list byte;
      exchange_for_physicals_flag : list byte;
      limited_details_flag : list byte;
      ld_full_details_flag : list byte;
      daily_aggregated_transaction_flag : list byte;
      da_full_details_flag : list byte;
      volume_omission_flag : list byte;
      vo_full_details_flag : list byte;
      four_weeks_aggregation_flag : list byte;
      fa_full_details_flag : list byte;
      indefinite_aggregation_flag : list byte;
      volume_omission_for_sovereign_debt_flag : list byte;
      consecutive_aggregation_flag : list byte;
      reserved_1 : N;
      venue_type : N;
      venue_book_definition_id : N;
      venue_measurement_unit_notation : list byte;
      quantity_in_measurement_unit : list byte;
      transaction_to_be_cleared : list byte;
      emission_allowance_type : list byte;
      venue_of_publication : list byte;
      market_mechanism : list byte;
      trading_mode : list byte;
      transaction_category : list byte;
      negotiation_indicator : list byte;
      agency_cross_indicator : list byte;
      modification_indicator : list byte;
      reference_price_indicator : list byte;
      special_dividend_indicator : list byte;
      off_book_automated_indicator : list byte;
      price_formation_indicator : list byte;
      algorithmic_indicator : list byte;
      post_trade_deferral_reason : list byte;
      deferral_enrichment_type : list byte;
      duplicative_indicator : list byte;
      third_country_trading_venue_of_execution : list byte;
      portfolio_transaction_flag : list byte;
      contingent_transaction_flag : list byte;
      price_conditions : list byte;
      market_closing_price_flag : list byte;
      nt_large_in_scale_flag : list byte;
      nt_pre_trade_transparency_flag : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (instrument record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (transaction_identification_code record) = 52 /\
      (total_number_of_transactions record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N /\
      (source_venue record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (mi_fid_price record) = 20 /\
      Datatypes.length (mi_fid_quantity record) = 20 /\
      Datatypes.length (mi_fid_trading_date_and_time record) = 27 /\
      Datatypes.length (instrument_identification_code_type record) = 4 /\
      Datatypes.length (instrument_identification_code record) = 12 /\
      Datatypes.length (price_notation record) = 4 /\
      Datatypes.length (price_currency record) = 3 /\
      Datatypes.length (notional_amount record) = 20 /\
      Datatypes.length (notional_currency record) = 3 /\
      Datatypes.length (venue_of_execution record) = 4 /\
      Datatypes.length (publication_date_and_time record) = 27 /\
      Datatypes.length (benchmark_transaction_flag record) = 4 /\
      Datatypes.length (agency_cross_trade_flag record) = 4 /\
      Datatypes.length (non_price_forming_transactions_flag record) = 4 /\
      Datatypes.length (non_price_contribution_to_discovery record) = 4 /\
      Datatypes.length (special_dividend_flag record) = 4 /\
      Datatypes.length (pt_deferral_reason_flag record) = 4 /\
      Datatypes.length (reference_price_transaction_flag record) = 4 /\
      Datatypes.length (nt_liquidity_flag record) = 4 /\
      Datatypes.length (nt_price_conditions_flag record) = 4 /\
      Datatypes.length (algo_transaction_flag record) = 4 /\
      Datatypes.length (pt_illiquid_flag record) = 4 /\
      Datatypes.length (price_improvement_flag record) = 4 /\
      Datatypes.length (cancellation_flag record) = 4 /\
      Datatypes.length (amendment_flag record) = 4 /\
      Datatypes.length (duplicate_flag record) = 4 /\
      Datatypes.length (exchange_for_physicals_flag record) = 4 /\
      Datatypes.length (limited_details_flag record) = 4 /\
      Datatypes.length (ld_full_details_flag record) = 4 /\
      Datatypes.length (daily_aggregated_transaction_flag record) = 4 /\
      Datatypes.length (da_full_details_flag record) = 4 /\
      Datatypes.length (volume_omission_flag record) = 4 /\
      Datatypes.length (vo_full_details_flag record) = 4 /\
      Datatypes.length (four_weeks_aggregation_flag record) = 4 /\
      Datatypes.length (fa_full_details_flag record) = 4 /\
      Datatypes.length (indefinite_aggregation_flag record) = 4 /\
      Datatypes.length (volume_omission_for_sovereign_debt_flag record) = 4 /\
      Datatypes.length (consecutive_aggregation_flag record) = 4 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (venue_type record < 256 ^ N.of_nat 1)%N /\
      (venue_book_definition_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (venue_measurement_unit_notation record) = 25 /\
      Datatypes.length (quantity_in_measurement_unit record) = 20 /\
      Datatypes.length (transaction_to_be_cleared record) = 1 /\
      Datatypes.length (emission_allowance_type record) = 4 /\
      Datatypes.length (venue_of_publication record) = 4 /\
      Datatypes.length (market_mechanism record) = 1 /\
      Datatypes.length (trading_mode record) = 1 /\
      Datatypes.length (transaction_category record) = 1 /\
      Datatypes.length (negotiation_indicator record) = 1 /\
      Datatypes.length (agency_cross_indicator record) = 1 /\
      Datatypes.length (modification_indicator record) = 1 /\
      Datatypes.length (reference_price_indicator record) = 1 /\
      Datatypes.length (special_dividend_indicator record) = 1 /\
      Datatypes.length (off_book_automated_indicator record) = 1 /\
      Datatypes.length (price_formation_indicator record) = 1 /\
      Datatypes.length (algorithmic_indicator record) = 1 /\
      Datatypes.length (post_trade_deferral_reason record) = 1 /\
      Datatypes.length (deferral_enrichment_type record) = 1 /\
      Datatypes.length (duplicative_indicator record) = 1 /\
      Datatypes.length (third_country_trading_venue_of_execution record) = 4 /\
      Datatypes.length (portfolio_transaction_flag record) = 4 /\
      Datatypes.length (contingent_transaction_flag record) = 4 /\
      Datatypes.length (price_conditions record) = 4 /\
      Datatypes.length (market_closing_price_flag record) = 4 /\
      Datatypes.length (nt_large_in_scale_flag record) = 4 /\
      Datatypes.length (nt_pre_trade_transparency_flag record) = 4.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (instrument record) ++
      encode_bytes 52 (transaction_identification_code record) ++
      encode_uint 4 (total_number_of_transactions record) ++
      encode_uint 8 (reserved_8 record) ++
      encode_uint 2 (source_venue record) ++
      encode_bytes 20 (mi_fid_price record) ++
      encode_bytes 20 (mi_fid_quantity record) ++
      encode_bytes 27 (mi_fid_trading_date_and_time record) ++
      encode_bytes 4 (instrument_identification_code_type record) ++
      encode_bytes 12 (instrument_identification_code record) ++
      encode_bytes 4 (price_notation record) ++
      encode_bytes 3 (price_currency record) ++
      encode_bytes 20 (notional_amount record) ++
      encode_bytes 3 (notional_currency record) ++
      encode_bytes 4 (venue_of_execution record) ++
      encode_bytes 27 (publication_date_and_time record) ++
      encode_bytes 4 (benchmark_transaction_flag record) ++
      encode_bytes 4 (agency_cross_trade_flag record) ++
      encode_bytes 4 (non_price_forming_transactions_flag record) ++
      encode_bytes 4 (non_price_contribution_to_discovery record) ++
      encode_bytes 4 (special_dividend_flag record) ++
      encode_bytes 4 (pt_deferral_reason_flag record) ++
      encode_bytes 4 (reference_price_transaction_flag record) ++
      encode_bytes 4 (nt_liquidity_flag record) ++
      encode_bytes 4 (nt_price_conditions_flag record) ++
      encode_bytes 4 (algo_transaction_flag record) ++
      encode_bytes 4 (pt_illiquid_flag record) ++
      encode_bytes 4 (price_improvement_flag record) ++
      encode_bytes 4 (cancellation_flag record) ++
      encode_bytes 4 (amendment_flag record) ++
      encode_bytes 4 (duplicate_flag record) ++
      encode_bytes 4 (exchange_for_physicals_flag record) ++
      encode_bytes 4 (limited_details_flag record) ++
      encode_bytes 4 (ld_full_details_flag record) ++
      encode_bytes 4 (daily_aggregated_transaction_flag record) ++
      encode_bytes 4 (da_full_details_flag record) ++
      encode_bytes 4 (volume_omission_flag record) ++
      encode_bytes 4 (vo_full_details_flag record) ++
      encode_bytes 4 (four_weeks_aggregation_flag record) ++
      encode_bytes 4 (fa_full_details_flag record) ++
      encode_bytes 4 (indefinite_aggregation_flag record) ++
      encode_bytes 4 (volume_omission_for_sovereign_debt_flag record) ++
      encode_bytes 4 (consecutive_aggregation_flag record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 1 (venue_type record) ++
      encode_uint 1 (venue_book_definition_id record) ++
      encode_bytes 25 (venue_measurement_unit_notation record) ++
      encode_bytes 20 (quantity_in_measurement_unit record) ++
      encode_bytes 1 (transaction_to_be_cleared record) ++
      encode_bytes 4 (emission_allowance_type record) ++
      encode_bytes 4 (venue_of_publication record) ++
      encode_bytes 1 (market_mechanism record) ++
      encode_bytes 1 (trading_mode record) ++
      encode_bytes 1 (transaction_category record) ++
      encode_bytes 1 (negotiation_indicator record) ++
      encode_bytes 1 (agency_cross_indicator record) ++
      encode_bytes 1 (modification_indicator record) ++
      encode_bytes 1 (reference_price_indicator record) ++
      encode_bytes 1 (special_dividend_indicator record) ++
      encode_bytes 1 (off_book_automated_indicator record) ++
      encode_bytes 1 (price_formation_indicator record) ++
      encode_bytes 1 (algorithmic_indicator record) ++
      encode_bytes 1 (post_trade_deferral_reason record) ++
      encode_bytes 1 (deferral_enrichment_type record) ++
      encode_bytes 1 (duplicative_indicator record) ++
      encode_bytes 4 (third_country_trading_venue_of_execution record) ++
      encode_bytes 4 (portfolio_transaction_flag record) ++
      encode_bytes 4 (contingent_transaction_flag record) ++
      encode_bytes 4 (price_conditions record) ++
      encode_bytes 4 (market_closing_price_flag record) ++
      encode_bytes 4 (nt_large_in_scale_flag record) ++
      encode_bytes 4 (nt_pre_trade_transparency_flag record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_bytes 52 bytes with
              | None => None
              | Some (transaction_identification_code_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (total_number_of_transactions_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (reserved_8_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (source_venue_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (mi_fid_price_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (mi_fid_quantity_value, bytes) =>
                                      match decode_bytes 27 bytes with
                                      | None => None
                                      | Some (mi_fid_trading_date_and_time_value, bytes) =>
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (instrument_identification_code_type_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (instrument_identification_code_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (price_notation_value, bytes) =>
                                                      match decode_bytes 3 bytes with
                                                      | None => None
                                                      | Some (price_currency_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (notional_amount_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (notional_currency_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (venue_of_execution_value, bytes) =>
                                                                      match decode_bytes 27 bytes with
                                                                      | None => None
                                                                      | Some (publication_date_and_time_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (benchmark_transaction_flag_value, bytes) =>
                                                                              match decode_bytes 4 bytes with
                                                                              | None => None
                                                                              | Some (agency_cross_trade_flag_value, bytes) =>
                                                                                  match decode_bytes 4 bytes with
                                                                                  | None => None
                                                                                  | Some (non_price_forming_transactions_flag_value, bytes) =>
                                                                                      match decode_bytes 4 bytes with
                                                                                      | None => None
                                                                                      | Some (non_price_contribution_to_discovery_value, bytes) =>
                                                                                          match decode_bytes 4 bytes with
                                                                                          | None => None
                                                                                          | Some (special_dividend_flag_value, bytes) =>
                                                                                              match decode_bytes 4 bytes with
                                                                                              | None => None
                                                                                              | Some (pt_deferral_reason_flag_value, bytes) =>
                                                                                                  match decode_bytes 4 bytes with
                                                                                                  | None => None
                                                                                                  | Some (reference_price_transaction_flag_value, bytes) =>
                                                                                                      match decode_bytes 4 bytes with
                                                                                                      | None => None
                                                                                                      | Some (nt_liquidity_flag_value, bytes) =>
                                                                                                          match decode_bytes 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (nt_price_conditions_flag_value, bytes) =>
                                                                                                              match decode_bytes 4 bytes with
                                                                                                              | None => None
                                                                                                              | Some (algo_transaction_flag_value, bytes) =>
                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (pt_illiquid_flag_value, bytes) =>
                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (price_improvement_flag_value, bytes) =>
                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (cancellation_flag_value, bytes) =>
                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (amendment_flag_value, bytes) =>
                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (duplicate_flag_value, bytes) =>
                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (exchange_for_physicals_flag_value, bytes) =>
                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (limited_details_flag_value, bytes) =>
                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (ld_full_details_flag_value, bytes) =>
                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (daily_aggregated_transaction_flag_value, bytes) =>
                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (da_full_details_flag_value, bytes) =>
                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (volume_omission_flag_value, bytes) =>
                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (vo_full_details_flag_value, bytes) =>
                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (four_weeks_aggregation_flag_value, bytes) =>
                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (fa_full_details_flag_value, bytes) =>
                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (indefinite_aggregation_flag_value, bytes) =>
                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (volume_omission_for_sovereign_debt_flag_value, bytes) =>
                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (consecutive_aggregation_flag_value, bytes) =>
                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (reserved_1_value, bytes) =>
                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (venue_type_value, bytes) =>
                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (venue_book_definition_id_value, bytes) =>
                                                                                                                                                                                                  match decode_bytes 25 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (venue_measurement_unit_notation_value, bytes) =>
                                                                                                                                                                                                      match decode_bytes 20 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (quantity_in_measurement_unit_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (transaction_to_be_cleared_value, bytes) =>
                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (emission_allowance_type_value, bytes) =>
                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (venue_of_publication_value, bytes) =>
                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (market_mechanism_value, bytes) =>
                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (trading_mode_value, bytes) =>
                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (transaction_category_value, bytes) =>
                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (negotiation_indicator_value, bytes) =>
                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (agency_cross_indicator_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (modification_indicator_value, bytes) =>
                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (reference_price_indicator_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (special_dividend_indicator_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (off_book_automated_indicator_value, bytes) =>
                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                          | Some (price_formation_indicator_value, bytes) =>
                                                                                                                                                                                                                                                              match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                              | Some (algorithmic_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                  match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                  | Some (post_trade_deferral_reason_value, bytes) =>
                                                                                                                                                                                                                                                                      match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                      | Some (deferral_enrichment_type_value, bytes) =>
                                                                                                                                                                                                                                                                          match decode_bytes 1 bytes with
                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                          | Some (duplicative_indicator_value, bytes) =>
                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                              | Some (third_country_trading_venue_of_execution_value, bytes) =>
                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                  | Some (portfolio_transaction_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                      | Some (contingent_transaction_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                          match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                                                                          | Some (price_conditions_value, bytes) =>
                                                                                                                                                                                                                                                                                              match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                                                                              | Some (market_closing_price_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                  match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                                                                  | Some (nt_large_in_scale_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                      match decode_bytes 4 bytes with
                                                                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                                                                      | Some (nt_pre_trade_transparency_flag_value, bytes) =>
                                                                                                                                                                                                                                                                                                          Some ({| timestamp := timestamp_value; instrument := instrument_value; transaction_identification_code := transaction_identification_code_value; total_number_of_transactions := total_number_of_transactions_value; reserved_8 := reserved_8_value; source_venue := source_venue_value; mi_fid_price := mi_fid_price_value; mi_fid_quantity := mi_fid_quantity_value; mi_fid_trading_date_and_time := mi_fid_trading_date_and_time_value; instrument_identification_code_type := instrument_identification_code_type_value; instrument_identification_code := instrument_identification_code_value; price_notation := price_notation_value; price_currency := price_currency_value; notional_amount := notional_amount_value; notional_currency := notional_currency_value; venue_of_execution := venue_of_execution_value; publication_date_and_time := publication_date_and_time_value; benchmark_transaction_flag := benchmark_transaction_flag_value; agency_cross_trade_flag := agency_cross_trade_flag_value; non_price_forming_transactions_flag := non_price_forming_transactions_flag_value; non_price_contribution_to_discovery := non_price_contribution_to_discovery_value; special_dividend_flag := special_dividend_flag_value; pt_deferral_reason_flag := pt_deferral_reason_flag_value; reference_price_transaction_flag := reference_price_transaction_flag_value; nt_liquidity_flag := nt_liquidity_flag_value; nt_price_conditions_flag := nt_price_conditions_flag_value; algo_transaction_flag := algo_transaction_flag_value; pt_illiquid_flag := pt_illiquid_flag_value; price_improvement_flag := price_improvement_flag_value; cancellation_flag := cancellation_flag_value; amendment_flag := amendment_flag_value; duplicate_flag := duplicate_flag_value; exchange_for_physicals_flag := exchange_for_physicals_flag_value; limited_details_flag := limited_details_flag_value; ld_full_details_flag := ld_full_details_flag_value; daily_aggregated_transaction_flag := daily_aggregated_transaction_flag_value; da_full_details_flag := da_full_details_flag_value; volume_omission_flag := volume_omission_flag_value; vo_full_details_flag := vo_full_details_flag_value; four_weeks_aggregation_flag := four_weeks_aggregation_flag_value; fa_full_details_flag := fa_full_details_flag_value; indefinite_aggregation_flag := indefinite_aggregation_flag_value; volume_omission_for_sovereign_debt_flag := volume_omission_for_sovereign_debt_flag_value; consecutive_aggregation_flag := consecutive_aggregation_flag_value; reserved_1 := reserved_1_value; venue_type := venue_type_value; venue_book_definition_id := venue_book_definition_id_value; venue_measurement_unit_notation := venue_measurement_unit_notation_value; quantity_in_measurement_unit := quantity_in_measurement_unit_value; transaction_to_be_cleared := transaction_to_be_cleared_value; emission_allowance_type := emission_allowance_type_value; venue_of_publication := venue_of_publication_value; market_mechanism := market_mechanism_value; trading_mode := trading_mode_value; transaction_category := transaction_category_value; negotiation_indicator := negotiation_indicator_value; agency_cross_indicator := agency_cross_indicator_value; modification_indicator := modification_indicator_value; reference_price_indicator := reference_price_indicator_value; special_dividend_indicator := special_dividend_indicator_value; off_book_automated_indicator := off_book_automated_indicator_value; price_formation_indicator := price_formation_indicator_value; algorithmic_indicator := algorithmic_indicator_value; post_trade_deferral_reason := post_trade_deferral_reason_value; deferral_enrichment_type := deferral_enrichment_type_value; duplicative_indicator := duplicative_indicator_value; third_country_trading_venue_of_execution := third_country_trading_venue_of_execution_value; portfolio_transaction_flag := portfolio_transaction_flag_value; contingent_transaction_flag := contingent_transaction_flag_value; price_conditions := price_conditions_value; market_closing_price_flag := market_closing_price_flag_value; nt_large_in_scale_flag := nt_large_in_scale_flag_value; nt_pre_trade_transparency_flag := nt_pre_trade_transparency_flag_value |}, bytes)
                                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 433.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 [bound_60 [bound_61 [bound_62 [bound_63 [bound_64 [bound_65 [bound_66 [bound_67 [bound_68 [bound_69 [bound_70 [bound_71 bound_72]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_bytes by exact bound_19.
      rewrite decode_encode_bytes by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_bytes by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      rewrite decode_encode_bytes by exact bound_26.
      rewrite decode_encode_bytes by exact bound_27.
      rewrite decode_encode_bytes by exact bound_28.
      rewrite decode_encode_bytes by exact bound_29.
      rewrite decode_encode_bytes by exact bound_30.
      rewrite decode_encode_bytes by exact bound_31.
      rewrite decode_encode_bytes by exact bound_32.
      rewrite decode_encode_bytes by exact bound_33.
      rewrite decode_encode_bytes by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_bytes by exact bound_36.
      rewrite decode_encode_bytes by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_bytes by exact bound_41.
      rewrite decode_encode_bytes by exact bound_42.
      rewrite decode_encode_bytes by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_bytes by exact bound_47.
      rewrite decode_encode_bytes by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_bytes by exact bound_50.
      rewrite decode_encode_bytes by exact bound_51.
      rewrite decode_encode_bytes by exact bound_52.
      rewrite decode_encode_bytes by exact bound_53.
      rewrite decode_encode_bytes by exact bound_54.
      rewrite decode_encode_bytes by exact bound_55.
      rewrite decode_encode_bytes by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_bytes by exact bound_58.
      rewrite decode_encode_bytes by exact bound_59.
      rewrite decode_encode_bytes by exact bound_60.
      rewrite decode_encode_bytes by exact bound_61.
      rewrite decode_encode_bytes by exact bound_62.
      rewrite decode_encode_bytes by exact bound_63.
      rewrite decode_encode_bytes by exact bound_64.
      rewrite decode_encode_bytes by exact bound_65.
      rewrite decode_encode_bytes by exact bound_66.
      rewrite decode_encode_bytes by exact bound_67.
      rewrite decode_encode_bytes by exact bound_68.
      rewrite decode_encode_bytes by exact bound_69.
      rewrite decode_encode_bytes by exact bound_70.
      rewrite decode_encode_bytes by exact bound_71.
      rewrite decode_encode_bytes by exact bound_72.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MifidIiTradeReportMessage.

End TradeEchoMifid2PostTradeRecoveryV244.
