From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Giełda Papierów Wartościowych w Warszawie Warsaw Stock Exchange Full Depth Replay

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
      - a field read in bits
      - a run counted by a field
  *)

Module WseReplayFullDepthV17620Tcp.

  Module MessageHeader.

    (** Every market data message opens with the same 42 byte header *)
    Record t := {
      message_length : N;
      message_type : N;
      message_version : N;
      sequence_number : N;
      timestamp : N;
      source_timestamp : N;
      is_encrypted : N;
      encryption_offset : N;
      encryption_key_id : N;
      session_id : N;
      stream_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 2)%N /\
      (message_version record < 256 ^ N.of_nat 2)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (source_timestamp record < 256 ^ N.of_nat 8)%N /\
      (is_encrypted record < 256 ^ N.of_nat 1)%N /\
      (encryption_offset record < 256 ^ N.of_nat 8)%N /\
      (encryption_key_id record < 256 ^ N.of_nat 4)%N /\
      (session_id record < 256 ^ N.of_nat 2)%N /\
      (stream_id record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_uint 2 (message_type record) ++
      encode_uint 2 (message_version record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (source_timestamp record) ++
      encode_uint 1 (is_encrypted record) ++
      encode_uint 8 (encryption_offset record) ++
      encode_uint 4 (encryption_key_id record) ++
      encode_uint 2 (session_id record) ++
      encode_uint 1 (stream_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_version_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (source_timestamp_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (is_encrypted_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (encryption_offset_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (encryption_key_id_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (session_id_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (stream_id_value, bytes) =>
                                                  Some ({| message_length := message_length_value; message_type := message_type_value; message_version := message_version_value; sequence_number := sequence_number_value; timestamp := timestamp_value; source_timestamp := source_timestamp_value; is_encrypted := is_encrypted_value; encryption_offset := encryption_offset_value; encryption_key_id := encryption_key_id_value; session_id := session_id_value; stream_id := stream_id_value |}, bytes)
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module WeekPlan.

    (** Trading week plan *)
    Record t := {
      calendar_id : N;
      weekdays : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (calendar_id record < 256 ^ N.of_nat 4)%N /\
      (weekdays record < 256 ^ N.of_nat 7)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (calendar_id record) ++
      encode_uint 7 (weekdays record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (calendar_id_value, bytes) =>
          match decode_uint 7 bytes with
          | None => None
          | Some (weekdays_value, bytes) =>
              Some ({| calendar_id := calendar_id_value; weekdays := weekdays_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End WeekPlan.

  Module CalendarException.

    (** Upcoming calendar day exception *)
    Record t := {
      calendar_id : N;
      calendar_exception_date : N;
      calendar_exception_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (calendar_id record < 256 ^ N.of_nat 4)%N /\
      (calendar_exception_date record < 256 ^ N.of_nat 4)%N /\
      (calendar_exception_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (calendar_id record) ++
      encode_uint 4 (calendar_exception_date record) ++
      encode_uint 1 (calendar_exception_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (calendar_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (calendar_exception_date_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (calendar_exception_type_value, bytes) =>
                  Some ({| calendar_id := calendar_id_value; calendar_exception_date := calendar_exception_date_value; calendar_exception_type := calendar_exception_type_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End CalendarException.

  Module TickTableEntry.

    (** Tick size definition *)
    Record t := {
      tick_size : N;
      lower_bound : N;
      tick_table_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tick_size record < 256 ^ N.of_nat 8)%N /\
      (lower_bound record < 256 ^ N.of_nat 8)%N /\
      (tick_table_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (tick_size record) ++
      encode_uint 8 (lower_bound record) ++
      encode_uint 4 (tick_table_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (tick_size_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (lower_bound_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (tick_table_id_value, bytes) =>
                  Some ({| tick_size := tick_size_value; lower_bound := lower_bound_value; tick_table_id := tick_table_id_value |}, bytes)
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

  End TickTableEntry.

  Module CollarTableEntry.

    (** Collar table definition *)
    Record t := {
      collar_table_id : N;
      collar_mode : N;
      collar_expression : N;
      collar_lower_bound : N;
      collar_value : N;
      collar_lower_bid : N;
      collar_upper_bid : N;
      collar_upper_ask : N;
      collar_lower_ask : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (collar_table_id record < 256 ^ N.of_nat 4)%N /\
      (collar_mode record < 256 ^ N.of_nat 1)%N /\
      (collar_expression record < 256 ^ N.of_nat 1)%N /\
      (collar_lower_bound record < 256 ^ N.of_nat 8)%N /\
      (collar_value record < 256 ^ N.of_nat 8)%N /\
      (collar_lower_bid record < 256 ^ N.of_nat 8)%N /\
      (collar_upper_bid record < 256 ^ N.of_nat 8)%N /\
      (collar_upper_ask record < 256 ^ N.of_nat 8)%N /\
      (collar_lower_ask record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (collar_table_id record) ++
      encode_uint 1 (collar_mode record) ++
      encode_uint 1 (collar_expression record) ++
      encode_uint 8 (collar_lower_bound record) ++
      encode_uint 8 (collar_value record) ++
      encode_uint 8 (collar_lower_bid record) ++
      encode_uint 8 (collar_upper_bid record) ++
      encode_uint 8 (collar_upper_ask record) ++
      encode_uint 8 (collar_lower_ask record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (collar_table_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (collar_mode_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (collar_expression_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (collar_lower_bound_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (collar_value_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (collar_lower_bid_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (collar_upper_bid_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (collar_upper_ask_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (collar_lower_ask_value, bytes) =>
                                          Some ({| collar_table_id := collar_table_id_value; collar_mode := collar_mode_value; collar_expression := collar_expression_value; collar_lower_bound := collar_lower_bound_value; collar_value := collar_value_value; collar_lower_bid := collar_lower_bid_value; collar_upper_bid := collar_upper_bid_value; collar_upper_ask := collar_upper_ask_value; collar_lower_ask := collar_lower_ask_value |}, bytes)
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

  End CollarTableEntry.

  Module TradingPhaseScheduleEntry.

    (** Trading phase definition *)
    Record t := {
      trading_schedule_id : N;
      trading_phase_id : N;
      trading_phase_settlement_cycle : N;
      trading_phase_max_block_settlement_cycle : N;
      static_collar_volatility_auction_id : N;
      dynamic_collar_volatility_auction_id : N;
      trading_phase_start_time : N;
      trading_phase_type : N;
      uncrossing : N;
      ext_static_collar_volatility_auction_id : N;
      ext_dynamic_collar_volatility_auction_id : N;
      clat_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trading_schedule_id record < 256 ^ N.of_nat 4)%N /\
      (trading_phase_id record < 256 ^ N.of_nat 4)%N /\
      (trading_phase_settlement_cycle record < 256 ^ N.of_nat 1)%N /\
      (trading_phase_max_block_settlement_cycle record < 256 ^ N.of_nat 1)%N /\
      (static_collar_volatility_auction_id record < 256 ^ N.of_nat 4)%N /\
      (dynamic_collar_volatility_auction_id record < 256 ^ N.of_nat 4)%N /\
      (trading_phase_start_time record < 256 ^ N.of_nat 8)%N /\
      (trading_phase_type record < 256 ^ N.of_nat 1)%N /\
      (uncrossing record < 256 ^ N.of_nat 1)%N /\
      (ext_static_collar_volatility_auction_id record < 256 ^ N.of_nat 4)%N /\
      (ext_dynamic_collar_volatility_auction_id record < 256 ^ N.of_nat 4)%N /\
      (clat_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (trading_schedule_id record) ++
      encode_uint 4 (trading_phase_id record) ++
      encode_uint 1 (trading_phase_settlement_cycle record) ++
      encode_uint 1 (trading_phase_max_block_settlement_cycle record) ++
      encode_uint 4 (static_collar_volatility_auction_id record) ++
      encode_uint 4 (dynamic_collar_volatility_auction_id record) ++
      encode_uint 8 (trading_phase_start_time record) ++
      encode_uint 1 (trading_phase_type record) ++
      encode_uint 1 (uncrossing record) ++
      encode_uint 4 (ext_static_collar_volatility_auction_id record) ++
      encode_uint 4 (ext_dynamic_collar_volatility_auction_id record) ++
      encode_uint 4 (clat_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (trading_schedule_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trading_phase_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_phase_settlement_cycle_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trading_phase_max_block_settlement_cycle_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (static_collar_volatility_auction_id_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (dynamic_collar_volatility_auction_id_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trading_phase_start_time_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (trading_phase_type_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (uncrossing_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (ext_static_collar_volatility_auction_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (ext_dynamic_collar_volatility_auction_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (clat_id_value, bytes) =>
                                                      Some ({| trading_schedule_id := trading_schedule_id_value; trading_phase_id := trading_phase_id_value; trading_phase_settlement_cycle := trading_phase_settlement_cycle_value; trading_phase_max_block_settlement_cycle := trading_phase_max_block_settlement_cycle_value; static_collar_volatility_auction_id := static_collar_volatility_auction_id_value; dynamic_collar_volatility_auction_id := dynamic_collar_volatility_auction_id_value; trading_phase_start_time := trading_phase_start_time_value; trading_phase_type := trading_phase_type_value; uncrossing := uncrossing_value; ext_static_collar_volatility_auction_id := ext_static_collar_volatility_auction_id_value; ext_dynamic_collar_volatility_auction_id := ext_dynamic_collar_volatility_auction_id_value; clat_id := clat_id_value |}, bytes)
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
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
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TradingPhaseScheduleEntry.

  Module MarketStructure.

    (** Messages defining the Trading Venue’s market structure *)
    Record t := {
      id : N;
      parent_id : N;
      mic : list byte;
      name : list byte;
      market_model_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (id record < 256 ^ N.of_nat 4)%N /\
      (parent_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mic record) = 4 /\
      Datatypes.length (name record) = 50 /\
      (market_model_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (id record) ++
      encode_uint 4 (parent_id record) ++
      encode_bytes 4 (mic record) ++
      encode_bytes 50 (name record) ++
      encode_uint 1 (market_model_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (parent_id_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (mic_value, bytes) =>
                  match decode_bytes 50 bytes with
                  | None => None
                  | Some (name_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (market_model_type_value, bytes) =>
                          Some ({| id := id_value; parent_id := parent_id_value; mic := mic_value; name := name_value; market_model_type := market_model_type_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStructure.

  Module CollarGroup.

    (** Message defining a collar group *)
    Record t := {
      id : N;
      order_static_collar_table_id : N;
      order_dynamic_collar_table_id : N;
      trade_static_collar_table_id : N;
      trade_dynamic_collar_table_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (id record < 256 ^ N.of_nat 4)%N /\
      (order_static_collar_table_id record < 256 ^ N.of_nat 4)%N /\
      (order_dynamic_collar_table_id record < 256 ^ N.of_nat 4)%N /\
      (trade_static_collar_table_id record < 256 ^ N.of_nat 4)%N /\
      (trade_dynamic_collar_table_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (id record) ++
      encode_uint 4 (order_static_collar_table_id record) ++
      encode_uint 4 (order_dynamic_collar_table_id record) ++
      encode_uint 4 (trade_static_collar_table_id record) ++
      encode_uint 4 (trade_dynamic_collar_table_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (order_static_collar_table_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (order_dynamic_collar_table_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_static_collar_table_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (trade_dynamic_collar_table_id_value, bytes) =>
                          Some ({| id := id_value; order_static_collar_table_id := order_static_collar_table_id_value; order_dynamic_collar_table_id := order_dynamic_collar_table_id_value; trade_static_collar_table_id := trade_static_collar_table_id_value; trade_dynamic_collar_table_id := trade_dynamic_collar_table_id_value |}, bytes)
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

  End CollarGroup.

  Module ExternalUnderlying.

    (** The message contains a list of underlyings not traded in WATS. It concerns underlyings for derivatives and structured products *)
    Record t := {
      external_underlying_id : N;
      product_identification_product_identification : list byte;
      product_identification_type : N;
      product_code : list byte;
      product_name : list byte;
      mic : list byte;
      nominal_currency : N;
      trading_currency : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (external_underlying_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (product_identification_product_identification record) = 30 /\
      (product_identification_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (product_code record) = 20 /\
      Datatypes.length (product_name record) = 50 /\
      Datatypes.length (mic record) = 4 /\
      (nominal_currency record < 256 ^ N.of_nat 2)%N /\
      (trading_currency record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (external_underlying_id record) ++
      encode_bytes 30 (product_identification_product_identification record) ++
      encode_uint 1 (product_identification_type record) ++
      encode_bytes 20 (product_code record) ++
      encode_bytes 50 (product_name record) ++
      encode_bytes 4 (mic record) ++
      encode_uint 2 (nominal_currency record) ++
      encode_uint 2 (trading_currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (external_underlying_id_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (product_identification_product_identification_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (product_identification_type_value, bytes) =>
                  match decode_bytes 20 bytes with
                  | None => None
                  | Some (product_code_value, bytes) =>
                      match decode_bytes 50 bytes with
                      | None => None
                      | Some (product_name_value, bytes) =>
                          match decode_bytes 4 bytes with
                          | None => None
                          | Some (mic_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (nominal_currency_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (trading_currency_value, bytes) =>
                                      Some ({| external_underlying_id := external_underlying_id_value; product_identification_product_identification := product_identification_product_identification_value; product_identification_type := product_identification_type_value; product_code := product_code_value; product_name := product_name_value; mic := mic_value; nominal_currency := nominal_currency_value; trading_currency := trading_currency_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalUnderlying.

  Module Instrument.

    (** Definition of a financial instrument *)
    Record t := {
      instrument_id : N;
      product_type : N;
      product_subtype : N;
      first_trading_date : N;
      last_trading_date : N;
      product_id : N;
      currency : N;
      iceberg_min_value : N;
      lot_size : N;
      price_expression_type : N;
      calendar_id : N;
      market_structure_id : N;
      tick_table_id : N;
      reference_instrument_id : N;
      collar_group_id : N;
      trading_schedule_id : N;
      description : list byte;
      mic : list byte;
      nominal_value_price : N;
      nominal_value_type : N;
      multiplier_multiplier : N;
      strike_price : N;
      strike_price_currency : N;
      product_identification_product_identification : list byte;
      product_identification_type : N;
      settlement_calendar_id : N;
      bond_coupon_type : N;
      pre_trade_check_min_price : N;
      pre_trade_check_max_price : N;
      pre_trade_check_min_quantity : N;
      pre_trade_check_max_quantity : N;
      pre_trade_check_max_value : N;
      pre_trade_check_min_value : N;
      liquidity : N;
      market_model_type : N;
      issuer : list byte;
      issuer_reg_country : N;
      underlying_instrument_id : N;
      product_code : list byte;
      cfi : list byte;
      fisn : list byte;
      issue_size : N;
      nominal_currency : N;
      us_indicator : N;
      expiry_date : N;
      version_number : N;
      settlement_type : N;
      option_type : N;
      exercise_type : N;
      product_name : list byte;
      reference_price : N;
      status : N;
      initial_phase_id : N;
      threshold_max : N;
      threshold_min : N;
      is_leverage : N;
      accrued_interest_value : N;
      kid : list byte;
      kid_issue_date : N;
      value_at_risk : N;
      external_underlying_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (product_type record < 256 ^ N.of_nat 1)%N /\
      (product_subtype record < 256 ^ N.of_nat 1)%N /\
      (first_trading_date record < 256 ^ N.of_nat 4)%N /\
      (last_trading_date record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (currency record < 256 ^ N.of_nat 2)%N /\
      (iceberg_min_value record < 256 ^ N.of_nat 8)%N /\
      (lot_size record < 256 ^ N.of_nat 4)%N /\
      (price_expression_type record < 256 ^ N.of_nat 1)%N /\
      (calendar_id record < 256 ^ N.of_nat 4)%N /\
      (market_structure_id record < 256 ^ N.of_nat 4)%N /\
      (tick_table_id record < 256 ^ N.of_nat 4)%N /\
      (reference_instrument_id record < 256 ^ N.of_nat 4)%N /\
      (collar_group_id record < 256 ^ N.of_nat 4)%N /\
      (trading_schedule_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (description record) = 64 /\
      Datatypes.length (mic record) = 4 /\
      (nominal_value_price record < 256 ^ N.of_nat 8)%N /\
      (nominal_value_type record < 256 ^ N.of_nat 1)%N /\
      (multiplier_multiplier record < 256 ^ N.of_nat 8)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      (strike_price_currency record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (product_identification_product_identification record) = 30 /\
      (product_identification_type record < 256 ^ N.of_nat 1)%N /\
      (settlement_calendar_id record < 256 ^ N.of_nat 4)%N /\
      (bond_coupon_type record < 256 ^ N.of_nat 1)%N /\
      (pre_trade_check_min_price record < 256 ^ N.of_nat 8)%N /\
      (pre_trade_check_max_price record < 256 ^ N.of_nat 8)%N /\
      (pre_trade_check_min_quantity record < 256 ^ N.of_nat 8)%N /\
      (pre_trade_check_max_quantity record < 256 ^ N.of_nat 8)%N /\
      (pre_trade_check_max_value record < 256 ^ N.of_nat 8)%N /\
      (pre_trade_check_min_value record < 256 ^ N.of_nat 8)%N /\
      (liquidity record < 256 ^ N.of_nat 1)%N /\
      (market_model_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (issuer record) = 150 /\
      (issuer_reg_country record < 256 ^ N.of_nat 2)%N /\
      (underlying_instrument_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (product_code record) = 20 /\
      Datatypes.length (cfi record) = 6 /\
      Datatypes.length (fisn record) = 35 /\
      (issue_size record < 256 ^ N.of_nat 8)%N /\
      (nominal_currency record < 256 ^ N.of_nat 2)%N /\
      (us_indicator record < 256 ^ N.of_nat 1)%N /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (version_number record < 256 ^ N.of_nat 1)%N /\
      (settlement_type record < 256 ^ N.of_nat 1)%N /\
      (option_type record < 256 ^ N.of_nat 1)%N /\
      (exercise_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (product_name record) = 50 /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (status record < 256 ^ N.of_nat 1)%N /\
      (initial_phase_id record < 256 ^ N.of_nat 4)%N /\
      (threshold_max record < 256 ^ N.of_nat 8)%N /\
      (threshold_min record < 256 ^ N.of_nat 8)%N /\
      (is_leverage record < 256 ^ N.of_nat 1)%N /\
      (accrued_interest_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (kid record) = 128 /\
      (kid_issue_date record < 256 ^ N.of_nat 4)%N /\
      (value_at_risk record < 256 ^ N.of_nat 1)%N /\
      (external_underlying_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (product_type record) ++
      encode_uint 1 (product_subtype record) ++
      encode_uint 4 (first_trading_date record) ++
      encode_uint 4 (last_trading_date record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 2 (currency record) ++
      encode_uint 8 (iceberg_min_value record) ++
      encode_uint 4 (lot_size record) ++
      encode_uint 1 (price_expression_type record) ++
      encode_uint 4 (calendar_id record) ++
      encode_uint 4 (market_structure_id record) ++
      encode_uint 4 (tick_table_id record) ++
      encode_uint 4 (reference_instrument_id record) ++
      encode_uint 4 (collar_group_id record) ++
      encode_uint 4 (trading_schedule_id record) ++
      encode_bytes 64 (description record) ++
      encode_bytes 4 (mic record) ++
      encode_uint 8 (nominal_value_price record) ++
      encode_uint 1 (nominal_value_type record) ++
      encode_uint 8 (multiplier_multiplier record) ++
      encode_uint 8 (strike_price record) ++
      encode_uint 2 (strike_price_currency record) ++
      encode_bytes 30 (product_identification_product_identification record) ++
      encode_uint 1 (product_identification_type record) ++
      encode_uint 4 (settlement_calendar_id record) ++
      encode_uint 1 (bond_coupon_type record) ++
      encode_uint 8 (pre_trade_check_min_price record) ++
      encode_uint 8 (pre_trade_check_max_price record) ++
      encode_uint 8 (pre_trade_check_min_quantity record) ++
      encode_uint 8 (pre_trade_check_max_quantity record) ++
      encode_uint 8 (pre_trade_check_max_value record) ++
      encode_uint 8 (pre_trade_check_min_value record) ++
      encode_uint 1 (liquidity record) ++
      encode_uint 1 (market_model_type record) ++
      encode_bytes 150 (issuer record) ++
      encode_uint 2 (issuer_reg_country record) ++
      encode_uint 4 (underlying_instrument_id record) ++
      encode_bytes 20 (product_code record) ++
      encode_bytes 6 (cfi record) ++
      encode_bytes 35 (fisn record) ++
      encode_uint 8 (issue_size record) ++
      encode_uint 2 (nominal_currency record) ++
      encode_uint 1 (us_indicator record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 1 (version_number record) ++
      encode_uint 1 (settlement_type record) ++
      encode_uint 1 (option_type record) ++
      encode_uint 1 (exercise_type record) ++
      encode_bytes 50 (product_name record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 1 (status record) ++
      encode_uint 4 (initial_phase_id record) ++
      encode_uint 8 (threshold_max record) ++
      encode_uint 8 (threshold_min record) ++
      encode_uint 1 (is_leverage record) ++
      encode_uint 8 (accrued_interest_value record) ++
      encode_bytes 128 (kid record) ++
      encode_uint 4 (kid_issue_date record) ++
      encode_uint 1 (value_at_risk record) ++
      encode_uint 4 (external_underlying_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (product_type_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (product_subtype_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (first_trading_date_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (last_trading_date_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (product_id_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (currency_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (iceberg_min_value_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (lot_size_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (price_expression_type_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (calendar_id_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (market_structure_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (tick_table_id_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (reference_instrument_id_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (collar_group_id_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (trading_schedule_id_value, bytes) =>
                                                                      match decode_bytes 64 bytes with
                                                                      | None => None
                                                                      | Some (description_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (mic_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (nominal_value_price_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (nominal_value_type_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (multiplier_multiplier_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (strike_price_value, bytes) =>
                                                                                              match decode_uint 2 bytes with
                                                                                              | None => None
                                                                                              | Some (strike_price_currency_value, bytes) =>
                                                                                                  match decode_bytes 30 bytes with
                                                                                                  | None => None
                                                                                                  | Some (product_identification_product_identification_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (product_identification_type_value, bytes) =>
                                                                                                          match decode_uint 4 bytes with
                                                                                                          | None => None
                                                                                                          | Some (settlement_calendar_id_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (bond_coupon_type_value, bytes) =>
                                                                                                                  match decode_uint 8 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (pre_trade_check_min_price_value, bytes) =>
                                                                                                                      match decode_uint 8 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (pre_trade_check_max_price_value, bytes) =>
                                                                                                                          match decode_uint 8 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (pre_trade_check_min_quantity_value, bytes) =>
                                                                                                                              match decode_uint 8 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (pre_trade_check_max_quantity_value, bytes) =>
                                                                                                                                  match decode_uint 8 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (pre_trade_check_max_value_value, bytes) =>
                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (pre_trade_check_min_value_value, bytes) =>
                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (liquidity_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (market_model_type_value, bytes) =>
                                                                                                                                                  match decode_bytes 150 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (issuer_value, bytes) =>
                                                                                                                                                      match decode_uint 2 bytes with
                                                                                                                                                      | None => None
                                                                                                                                                      | Some (issuer_reg_country_value, bytes) =>
                                                                                                                                                          match decode_uint 4 bytes with
                                                                                                                                                          | None => None
                                                                                                                                                          | Some (underlying_instrument_id_value, bytes) =>
                                                                                                                                                              match decode_bytes 20 bytes with
                                                                                                                                                              | None => None
                                                                                                                                                              | Some (product_code_value, bytes) =>
                                                                                                                                                                  match decode_bytes 6 bytes with
                                                                                                                                                                  | None => None
                                                                                                                                                                  | Some (cfi_value, bytes) =>
                                                                                                                                                                      match decode_bytes 35 bytes with
                                                                                                                                                                      | None => None
                                                                                                                                                                      | Some (fisn_value, bytes) =>
                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                          | None => None
                                                                                                                                                                          | Some (issue_size_value, bytes) =>
                                                                                                                                                                              match decode_uint 2 bytes with
                                                                                                                                                                              | None => None
                                                                                                                                                                              | Some (nominal_currency_value, bytes) =>
                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                  | None => None
                                                                                                                                                                                  | Some (us_indicator_value, bytes) =>
                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                      | None => None
                                                                                                                                                                                      | Some (expiry_date_value, bytes) =>
                                                                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                                                                          | None => None
                                                                                                                                                                                          | Some (version_number_value, bytes) =>
                                                                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                                                                              | None => None
                                                                                                                                                                                              | Some (settlement_type_value, bytes) =>
                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                  | Some (option_type_value, bytes) =>
                                                                                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                      | Some (exercise_type_value, bytes) =>
                                                                                                                                                                                                          match decode_bytes 50 bytes with
                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                          | Some (product_name_value, bytes) =>
                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                              | Some (reference_price_value, bytes) =>
                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                  | Some (status_value, bytes) =>
                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                      | Some (initial_phase_id_value, bytes) =>
                                                                                                                                                                                                                          match decode_uint 8 bytes with
                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                          | Some (threshold_max_value, bytes) =>
                                                                                                                                                                                                                              match decode_uint 8 bytes with
                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                              | Some (threshold_min_value, bytes) =>
                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                  | Some (is_leverage_value, bytes) =>
                                                                                                                                                                                                                                      match decode_uint 8 bytes with
                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                      | Some (accrued_interest_value_value, bytes) =>
                                                                                                                                                                                                                                          match decode_bytes 128 bytes with
                                                                                                                                                                                                                                          | None => None
                                                                                                                                                                                                                                          | Some (kid_value, bytes) =>
                                                                                                                                                                                                                                              match decode_uint 4 bytes with
                                                                                                                                                                                                                                              | None => None
                                                                                                                                                                                                                                              | Some (kid_issue_date_value, bytes) =>
                                                                                                                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                                                                                                                  | None => None
                                                                                                                                                                                                                                                  | Some (value_at_risk_value, bytes) =>
                                                                                                                                                                                                                                                      match decode_uint 4 bytes with
                                                                                                                                                                                                                                                      | None => None
                                                                                                                                                                                                                                                      | Some (external_underlying_id_value, bytes) =>
                                                                                                                                                                                                                                                          Some ({| instrument_id := instrument_id_value; product_type := product_type_value; product_subtype := product_subtype_value; first_trading_date := first_trading_date_value; last_trading_date := last_trading_date_value; product_id := product_id_value; currency := currency_value; iceberg_min_value := iceberg_min_value_value; lot_size := lot_size_value; price_expression_type := price_expression_type_value; calendar_id := calendar_id_value; market_structure_id := market_structure_id_value; tick_table_id := tick_table_id_value; reference_instrument_id := reference_instrument_id_value; collar_group_id := collar_group_id_value; trading_schedule_id := trading_schedule_id_value; description := description_value; mic := mic_value; nominal_value_price := nominal_value_price_value; nominal_value_type := nominal_value_type_value; multiplier_multiplier := multiplier_multiplier_value; strike_price := strike_price_value; strike_price_currency := strike_price_currency_value; product_identification_product_identification := product_identification_product_identification_value; product_identification_type := product_identification_type_value; settlement_calendar_id := settlement_calendar_id_value; bond_coupon_type := bond_coupon_type_value; pre_trade_check_min_price := pre_trade_check_min_price_value; pre_trade_check_max_price := pre_trade_check_max_price_value; pre_trade_check_min_quantity := pre_trade_check_min_quantity_value; pre_trade_check_max_quantity := pre_trade_check_max_quantity_value; pre_trade_check_max_value := pre_trade_check_max_value_value; pre_trade_check_min_value := pre_trade_check_min_value_value; liquidity := liquidity_value; market_model_type := market_model_type_value; issuer := issuer_value; issuer_reg_country := issuer_reg_country_value; underlying_instrument_id := underlying_instrument_id_value; product_code := product_code_value; cfi := cfi_value; fisn := fisn_value; issue_size := issue_size_value; nominal_currency := nominal_currency_value; us_indicator := us_indicator_value; expiry_date := expiry_date_value; version_number := version_number_value; settlement_type := settlement_type_value; option_type := option_type_value; exercise_type := exercise_type_value; product_name := product_name_value; reference_price := reference_price_value; status := status_value; initial_phase_id := initial_phase_id_value; threshold_max := threshold_max_value; threshold_min := threshold_min_value; is_leverage := is_leverage_value; accrued_interest_value := accrued_interest_value_value; kid := kid_value; kid_issue_date := kid_issue_date_value; value_at_risk := value_at_risk_value; external_underlying_id := external_underlying_id_value |}, bytes)
                                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                                              end
                                                                                                                                                                                                                                          end
                                                                                                                                                                                                                                      end
                                                                                                                                                                                                                                  end
                                                                                                                                                                                                                              end
                                                                                                                                                                                                                          end
                                                                                                                                                                                                                      end
                                                                                                                                                                                                                  end
                                                                                                                                                                                                              end
                                                                                                                                                                                                          end
                                                                                                                                                                                                      end
                                                                                                                                                                                                  end
                                                                                                                                                                                              end
                                                                                                                                                                                          end
                                                                                                                                                                                      end
                                                                                                                                                                                  end
                                                                                                                                                                              end
                                                                                                                                                                          end
                                                                                                                                                                      end
                                                                                                                                                                  end
                                                                                                                                                              end
                                                                                                                                                          end
                                                                                                                                                      end
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 699.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 [bound_35 [bound_36 [bound_37 [bound_38 [bound_39 [bound_40 [bound_41 [bound_42 [bound_43 [bound_44 [bound_45 [bound_46 [bound_47 [bound_48 [bound_49 [bound_50 [bound_51 [bound_52 [bound_53 [bound_54 [bound_55 [bound_56 [bound_57 [bound_58 [bound_59 bound_60]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
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
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_bytes by exact bound_35.
      rewrite decode_encode_uint by exact bound_36.
      rewrite decode_encode_uint by exact bound_37.
      rewrite decode_encode_bytes by exact bound_38.
      rewrite decode_encode_bytes by exact bound_39.
      rewrite decode_encode_bytes by exact bound_40.
      rewrite decode_encode_uint by exact bound_41.
      rewrite decode_encode_uint by exact bound_42.
      rewrite decode_encode_uint by exact bound_43.
      rewrite decode_encode_uint by exact bound_44.
      rewrite decode_encode_uint by exact bound_45.
      rewrite decode_encode_uint by exact bound_46.
      rewrite decode_encode_uint by exact bound_47.
      rewrite decode_encode_uint by exact bound_48.
      rewrite decode_encode_bytes by exact bound_49.
      rewrite decode_encode_uint by exact bound_50.
      rewrite decode_encode_uint by exact bound_51.
      rewrite decode_encode_uint by exact bound_52.
      rewrite decode_encode_uint by exact bound_53.
      rewrite decode_encode_uint by exact bound_54.
      rewrite decode_encode_uint by exact bound_55.
      rewrite decode_encode_uint by exact bound_56.
      rewrite decode_encode_bytes by exact bound_57.
      rewrite decode_encode_uint by exact bound_58.
      rewrite decode_encode_uint by exact bound_59.
      rewrite decode_encode_uint by exact bound_60.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Instrument.

  Module AccruedInterestTableEntry.

    (** Message describing an accrued interest table entry *)
    Record t := {
      product_id : N;
      accrued_interest_table_entry_date : N;
      accrued_interest_table_entry_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (accrued_interest_table_entry_date record < 256 ^ N.of_nat 4)%N /\
      (accrued_interest_table_entry_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (product_id record) ++
      encode_uint 4 (accrued_interest_table_entry_date record) ++
      encode_uint 8 (accrued_interest_table_entry_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (product_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (accrued_interest_table_entry_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (accrued_interest_table_entry_value_value, bytes) =>
                  Some ({| product_id := product_id_value; accrued_interest_table_entry_date := accrued_interest_table_entry_date_value; accrued_interest_table_entry_value := accrued_interest_table_entry_value_value |}, bytes)
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

  End AccruedInterestTableEntry.

  Module IndexationTableEntry.

    (** Message describing an indexation table entry *)
    Record t := {
      product_id : N;
      indexation_table_entry_date : N;
      indexation_table_entry_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (indexation_table_entry_date record < 256 ^ N.of_nat 4)%N /\
      (indexation_table_entry_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (product_id record) ++
      encode_uint 4 (indexation_table_entry_date record) ++
      encode_uint 8 (indexation_table_entry_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (product_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (indexation_table_entry_date_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (indexation_table_entry_value_value, bytes) =>
                  Some ({| product_id := product_id_value; indexation_table_entry_date := indexation_table_entry_date_value; indexation_table_entry_value := indexation_table_entry_value_value |}, bytes)
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

  End IndexationTableEntry.

  Module ProductIdentificationPublicProductIdentification.

    (** PublicProductIdentification *)
    Record t := {
      product_identification_product_identification : list byte;
      product_identification_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (product_identification_product_identification record) = 30 /\
      (product_identification_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 30 (product_identification_product_identification record) ++
      encode_uint 1 (product_identification_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 30 bytes with
      | None => None
      | Some (product_identification_product_identification_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (product_identification_type_value, bytes) =>
              Some ({| product_identification_product_identification := product_identification_product_identification_value; product_identification_type := product_identification_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ProductIdentificationPublicProductIdentification.

  Module IndexUnderlying.

    (** IndexUnderlying *)
    Record t := {
      product_identification_public_product_identification : ProductIdentificationPublicProductIdentification.t;
      index_underlying_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      ProductIdentificationPublicProductIdentification.bounded (product_identification_public_product_identification record) /\
      (index_underlying_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      ProductIdentificationPublicProductIdentification.encode (product_identification_public_product_identification record) ++
      encode_uint 1 (index_underlying_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match ProductIdentificationPublicProductIdentification.decode bytes with
      | None => None
      | Some (product_identification_public_product_identification_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (index_underlying_type_value, bytes) =>
              Some ({| product_identification_public_product_identification := product_identification_public_product_identification_value; index_underlying_type := index_underlying_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !ProductIdentificationPublicProductIdentification.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite ProductIdentificationPublicProductIdentification.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply ProductIdentificationPublicProductIdentification.eq_dec]. Defined.

  End IndexUnderlying.

  Module PublicProductIdentification.

    (** PublicProductIdentification *)
    Record t := {
      product_identification_product_identification : list byte;
      product_identification_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (product_identification_product_identification record) = 30 /\
      (product_identification_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 30 (product_identification_product_identification record) ++
      encode_uint 1 (product_identification_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 30 bytes with
      | None => None
      | Some (product_identification_product_identification_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (product_identification_type_value, bytes) =>
              Some ({| product_identification_product_identification := product_identification_product_identification_value; product_identification_type := product_identification_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PublicProductIdentification.

  Module AuctionSummary.

    (** Auction summary, including auction price and quantity *)
    Record t := {
      instrument_id : N;
      price : N;
      quantity : N;
      auction_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (auction_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 1 (auction_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (auction_type_value, bytes) =>
                      Some ({| instrument_id := instrument_id_value; price := price_value; quantity := quantity_value; auction_type := auction_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End AuctionSummary.

  Module AuctionUpdate.

    (** Updates IMP/IMV and BBO during an auction *)
    Record t := {
      instrument_id : N;
      indicative_matching_price : N;
      indicative_matching_volume : N;
      total_sell_quantity_at_imp : N;
      total_buy_quantity_at_imp : N;
      best_sell_level : N;
      best_sell_level_quantity : N;
      best_buy_level : N;
      best_buy_level_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (indicative_matching_price record < 256 ^ N.of_nat 8)%N /\
      (indicative_matching_volume record < 256 ^ N.of_nat 8)%N /\
      (total_sell_quantity_at_imp record < 256 ^ N.of_nat 8)%N /\
      (total_buy_quantity_at_imp record < 256 ^ N.of_nat 8)%N /\
      (best_sell_level record < 256 ^ N.of_nat 8)%N /\
      (best_sell_level_quantity record < 256 ^ N.of_nat 8)%N /\
      (best_buy_level record < 256 ^ N.of_nat 8)%N /\
      (best_buy_level_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (indicative_matching_price record) ++
      encode_uint 8 (indicative_matching_volume record) ++
      encode_uint 8 (total_sell_quantity_at_imp record) ++
      encode_uint 8 (total_buy_quantity_at_imp record) ++
      encode_uint 8 (best_sell_level record) ++
      encode_uint 8 (best_sell_level_quantity record) ++
      encode_uint 8 (best_buy_level record) ++
      encode_uint 8 (best_buy_level_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (indicative_matching_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (indicative_matching_volume_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (total_sell_quantity_at_imp_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (total_buy_quantity_at_imp_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (best_sell_level_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (best_sell_level_quantity_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (best_buy_level_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (best_buy_level_quantity_value, bytes) =>
                                          Some ({| instrument_id := instrument_id_value; indicative_matching_price := indicative_matching_price_value; indicative_matching_volume := indicative_matching_volume_value; total_sell_quantity_at_imp := total_sell_quantity_at_imp_value; total_buy_quantity_at_imp := total_buy_quantity_at_imp_value; best_sell_level := best_sell_level_value; best_sell_level_quantity := best_sell_level_quantity_value; best_buy_level := best_buy_level_value; best_buy_level_quantity := best_buy_level_quantity_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
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

  End AuctionUpdate.

  Module PriceLevel.

    (** PriceLevel *)
    Record t := {
      is_encrypted : N;
      encryption_offset : N;
      encryption_key_id : N;
      price : N;
      quantity : N;
      order_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (is_encrypted record < 256 ^ N.of_nat 1)%N /\
      (encryption_offset record < 256 ^ N.of_nat 8)%N /\
      (encryption_key_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (order_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (is_encrypted record) ++
      encode_uint 8 (encryption_offset record) ++
      encode_uint 4 (encryption_key_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 2 (order_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (is_encrypted_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (encryption_offset_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (encryption_key_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (order_count_value, bytes) =>
                              Some ({| is_encrypted := is_encrypted_value; encryption_offset := encryption_offset_value; encryption_key_id := encryption_key_id_value; price := price_value; quantity := quantity_value; order_count := order_count_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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

  End PriceLevel.

  Module PriceLevel2.

    (** PriceLevel *)
    Record t := {
      is_encrypted : N;
      encryption_offset : N;
      encryption_key_id : N;
      price : N;
      quantity : N;
      order_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (is_encrypted record < 256 ^ N.of_nat 1)%N /\
      (encryption_offset record < 256 ^ N.of_nat 8)%N /\
      (encryption_key_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (order_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (is_encrypted record) ++
      encode_uint 8 (encryption_offset record) ++
      encode_uint 4 (encryption_key_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 2 (order_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (is_encrypted_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (encryption_offset_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (encryption_key_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (order_count_value, bytes) =>
                              Some ({| is_encrypted := is_encrypted_value; encryption_offset := encryption_offset_value; encryption_key_id := encryption_key_id_value; price := price_value; quantity := quantity_value; order_count := order_count_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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

  End PriceLevel2.

  Module TopPriceLevelUpdate.

    (** BBO Level 1 *)
    Record t := {
      instrument_id : N;
      price : N;
      quantity : N;
      side : N;
      order_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (order_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 1 (side record) ++
      encode_uint 2 (order_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (order_count_value, bytes) =>
                          Some ({| instrument_id := instrument_id_value; price := price_value; quantity := quantity_value; side := side_value; order_count := order_count_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End TopPriceLevelUpdate.

  Module PublicProductIdentification2.

    (** PublicProductIdentification *)
    Record t := {
      product_identification_product_identification : list byte;
      product_identification_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (product_identification_product_identification record) = 30 /\
      (product_identification_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 30 (product_identification_product_identification record) ++
      encode_uint 1 (product_identification_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 30 bytes with
      | None => None
      | Some (product_identification_product_identification_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (product_identification_type_value, bytes) =>
              Some ({| product_identification_product_identification := product_identification_product_identification_value; product_identification_type := product_identification_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PublicProductIdentification2.

  Module Trade.

    (** Enriched trade report *)
    Record t := {
      instrument_id : N;
      settlement_value_value : N;
      settlement_date : N;
      trading_timestamp : N;
      public_product_identification : PublicProductIdentification2.t;
      price : N;
      price_currency : N;
      price_notation : N;
      quantity : N;
      nominal_value_value : N;
      nominal_currency : N;
      mic : list byte;
      publication_timestamp : N;
      trade_id : N;
      trade_to_be_cleared : N;
      pct_change : N;
      vwap : N;
      no_trades : N;
      total_volume : N;
      total_value : N;
      opening_price : N;
      max_price : N;
      min_price : N;
      mmt_market_mechanism : N;
      mmt_trading_mode : N;
      mmt_transaction_category : N;
      mmt_negotiation_indicator : N;
      mmt_agency_cross_trade_indicator : N;
      mmt_modification_indicator : N;
      mmt_benchmark_reference_price_indicator : N;
      mmt_special_dividend_indicator : N;
      mmt_off_book_automated_indicator : N;
      mmt_ordinary_trade_indicator : N;
      mmt_algorithmic_indicator : N;
      mmt_post_trade_deferral_reason : N;
      mmt_post_trade_deferral_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (settlement_value_value record < 256 ^ N.of_nat 8)%N /\
      (settlement_date record < 256 ^ N.of_nat 4)%N /\
      (trading_timestamp record < 256 ^ N.of_nat 8)%N /\
      PublicProductIdentification2.bounded (public_product_identification record) /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (price_currency record < 256 ^ N.of_nat 2)%N /\
      (price_notation record < 256 ^ N.of_nat 1)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (nominal_value_value record < 256 ^ N.of_nat 8)%N /\
      (nominal_currency record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (mic record) = 4 /\
      (publication_timestamp record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (trade_to_be_cleared record < 256 ^ N.of_nat 1)%N /\
      (pct_change record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (no_trades record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      (total_value record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (max_price record < 256 ^ N.of_nat 8)%N /\
      (min_price record < 256 ^ N.of_nat 8)%N /\
      (mmt_market_mechanism record < 256 ^ N.of_nat 1)%N /\
      (mmt_trading_mode record < 256 ^ N.of_nat 1)%N /\
      (mmt_transaction_category record < 256 ^ N.of_nat 1)%N /\
      (mmt_negotiation_indicator record < 256 ^ N.of_nat 1)%N /\
      (mmt_agency_cross_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (mmt_modification_indicator record < 256 ^ N.of_nat 1)%N /\
      (mmt_benchmark_reference_price_indicator record < 256 ^ N.of_nat 1)%N /\
      (mmt_special_dividend_indicator record < 256 ^ N.of_nat 1)%N /\
      (mmt_off_book_automated_indicator record < 256 ^ N.of_nat 1)%N /\
      (mmt_ordinary_trade_indicator record < 256 ^ N.of_nat 1)%N /\
      (mmt_algorithmic_indicator record < 256 ^ N.of_nat 1)%N /\
      (mmt_post_trade_deferral_reason record < 256 ^ N.of_nat 1)%N /\
      (mmt_post_trade_deferral_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (settlement_value_value record) ++
      encode_uint 4 (settlement_date record) ++
      encode_uint 8 (trading_timestamp record) ++
      PublicProductIdentification2.encode (public_product_identification record) ++
      encode_uint 8 (price record) ++
      encode_uint 2 (price_currency record) ++
      encode_uint 1 (price_notation record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 8 (nominal_value_value record) ++
      encode_uint 2 (nominal_currency record) ++
      encode_bytes 4 (mic record) ++
      encode_uint 8 (publication_timestamp record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 1 (trade_to_be_cleared record) ++
      encode_uint 8 (pct_change record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (no_trades record) ++
      encode_uint 8 (total_volume record) ++
      encode_uint 8 (total_value record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (max_price record) ++
      encode_uint 8 (min_price record) ++
      encode_uint 1 (mmt_market_mechanism record) ++
      encode_uint 1 (mmt_trading_mode record) ++
      encode_uint 1 (mmt_transaction_category record) ++
      encode_uint 1 (mmt_negotiation_indicator record) ++
      encode_uint 1 (mmt_agency_cross_trade_indicator record) ++
      encode_uint 1 (mmt_modification_indicator record) ++
      encode_uint 1 (mmt_benchmark_reference_price_indicator record) ++
      encode_uint 1 (mmt_special_dividend_indicator record) ++
      encode_uint 1 (mmt_off_book_automated_indicator record) ++
      encode_uint 1 (mmt_ordinary_trade_indicator record) ++
      encode_uint 1 (mmt_algorithmic_indicator record) ++
      encode_uint 1 (mmt_post_trade_deferral_reason record) ++
      encode_uint 1 (mmt_post_trade_deferral_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (settlement_value_value_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (settlement_date_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (trading_timestamp_value, bytes) =>
                      match PublicProductIdentification2.decode bytes with
                      | None => None
                      | Some (public_product_identification_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (price_currency_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (price_notation_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (quantity_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (nominal_value_value_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (nominal_currency_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (mic_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (publication_timestamp_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (trade_id_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (trade_to_be_cleared_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (pct_change_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (vwap_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (no_trades_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (total_volume_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (total_value_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (opening_price_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (max_price_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (min_price_value, bytes) =>
                                                                                                  match decode_uint 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (mmt_market_mechanism_value, bytes) =>
                                                                                                      match decode_uint 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (mmt_trading_mode_value, bytes) =>
                                                                                                          match decode_uint 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (mmt_transaction_category_value, bytes) =>
                                                                                                              match decode_uint 1 bytes with
                                                                                                              | None => None
                                                                                                              | Some (mmt_negotiation_indicator_value, bytes) =>
                                                                                                                  match decode_uint 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (mmt_agency_cross_trade_indicator_value, bytes) =>
                                                                                                                      match decode_uint 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (mmt_modification_indicator_value, bytes) =>
                                                                                                                          match decode_uint 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (mmt_benchmark_reference_price_indicator_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (mmt_special_dividend_indicator_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (mmt_off_book_automated_indicator_value, bytes) =>
                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (mmt_ordinary_trade_indicator_value, bytes) =>
                                                                                                                                          match decode_uint 1 bytes with
                                                                                                                                          | None => None
                                                                                                                                          | Some (mmt_algorithmic_indicator_value, bytes) =>
                                                                                                                                              match decode_uint 1 bytes with
                                                                                                                                              | None => None
                                                                                                                                              | Some (mmt_post_trade_deferral_reason_value, bytes) =>
                                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                                  | None => None
                                                                                                                                                  | Some (mmt_post_trade_deferral_type_value, bytes) =>
                                                                                                                                                      Some ({| instrument_id := instrument_id_value; settlement_value_value := settlement_value_value_value; settlement_date := settlement_date_value; trading_timestamp := trading_timestamp_value; public_product_identification := public_product_identification_value; price := price_value; price_currency := price_currency_value; price_notation := price_notation_value; quantity := quantity_value; nominal_value_value := nominal_value_value_value; nominal_currency := nominal_currency_value; mic := mic_value; publication_timestamp := publication_timestamp_value; trade_id := trade_id_value; trade_to_be_cleared := trade_to_be_cleared_value; pct_change := pct_change_value; vwap := vwap_value; no_trades := no_trades_value; total_volume := total_volume_value; total_value := total_value_value; opening_price := opening_price_value; max_price := max_price_value; min_price := min_price_value; mmt_market_mechanism := mmt_market_mechanism_value; mmt_trading_mode := mmt_trading_mode_value; mmt_transaction_category := mmt_transaction_category_value; mmt_negotiation_indicator := mmt_negotiation_indicator_value; mmt_agency_cross_trade_indicator := mmt_agency_cross_trade_indicator_value; mmt_modification_indicator := mmt_modification_indicator_value; mmt_benchmark_reference_price_indicator := mmt_benchmark_reference_price_indicator_value; mmt_special_dividend_indicator := mmt_special_dividend_indicator_value; mmt_off_book_automated_indicator := mmt_off_book_automated_indicator_value; mmt_ordinary_trade_indicator := mmt_ordinary_trade_indicator_value; mmt_algorithmic_indicator := mmt_algorithmic_indicator_value; mmt_post_trade_deferral_reason := mmt_post_trade_deferral_reason_value; mmt_post_trade_deferral_type := mmt_post_trade_deferral_type_value |}, bytes)
                                                                                                                                                  end
                                                                                                                                              end
                                                                                                                                          end
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 178.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !PublicProductIdentification2.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 [bound_32 [bound_33 [bound_34 bound_35]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite PublicProductIdentification2.decode_encode by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
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
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      rewrite decode_encode_uint by exact bound_33.
      rewrite decode_encode_uint by exact bound_34.
      rewrite decode_encode_uint by exact bound_35.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply PublicProductIdentification2.eq_dec]. Defined.

  End Trade.

  Module PublicProductIdentification3.

    (** PublicProductIdentification *)
    Record t := {
      product_identification_product_identification : list byte;
      product_identification_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (product_identification_product_identification record) = 30 /\
      (product_identification_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 30 (product_identification_product_identification record) ++
      encode_uint 1 (product_identification_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 30 bytes with
      | None => None
      | Some (product_identification_product_identification_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (product_identification_type_value, bytes) =>
              Some ({| product_identification_product_identification := product_identification_product_identification_value; product_identification_type := product_identification_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PublicProductIdentification3.

  Module PositionReport.

    (** Report of open positions *)
    Record t := {
      public_product_identification : PublicProductIdentification3.t;
      pos_type : N;
      open_positions : N;
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      PublicProductIdentification3.bounded (public_product_identification record) /\
      (pos_type record < 256 ^ N.of_nat 1)%N /\
      (open_positions record < 256 ^ N.of_nat 4)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      PublicProductIdentification3.encode (public_product_identification record) ++
      encode_uint 1 (pos_type record) ++
      encode_uint 4 (open_positions record) ++
      encode_uint 4 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match PublicProductIdentification3.decode bytes with
      | None => None
      | Some (public_product_identification_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (pos_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (open_positions_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      Some ({| public_product_identification := public_product_identification_value; pos_type := pos_type_value; open_positions := open_positions_value; trade_id := trade_id_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !PublicProductIdentification3.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite PublicProductIdentification3.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply PublicProductIdentification3.eq_dec]. Defined.

  End PositionReport.

  Module InstrumentStatusChange.

    (** Start of a new trading phase *)
    Record t := {
      instrument_id : N;
      trading_phase_id : N;
      trading_phase_type : N;
      status : N;
      stressed_market : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (trading_phase_id record < 256 ^ N.of_nat 4)%N /\
      (trading_phase_type record < 256 ^ N.of_nat 1)%N /\
      (status record < 256 ^ N.of_nat 1)%N /\
      (stressed_market record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 4 (trading_phase_id record) ++
      encode_uint 1 (trading_phase_type record) ++
      encode_uint 1 (status record) ++
      encode_uint 1 (stressed_market record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (trading_phase_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_phase_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (stressed_market_value, bytes) =>
                          Some ({| instrument_id := instrument_id_value; trading_phase_id := trading_phase_id_value; trading_phase_type := trading_phase_type_value; status := status_value; stressed_market := stressed_market_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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

  End InstrumentStatusChange.

  Module OrderCollars.

    (** New order price collars *)
    Record t := {
      instrument_id : N;
      collar_type : N;
      price : N;
      lower_bid : N;
      upper_bid : N;
      lower_ask : N;
      upper_ask : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (collar_type record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (lower_bid record < 256 ^ N.of_nat 8)%N /\
      (upper_bid record < 256 ^ N.of_nat 8)%N /\
      (lower_ask record < 256 ^ N.of_nat 8)%N /\
      (upper_ask record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (collar_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (lower_bid record) ++
      encode_uint 8 (upper_bid record) ++
      encode_uint 8 (lower_ask record) ++
      encode_uint 8 (upper_ask record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (collar_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (lower_bid_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (upper_bid_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (lower_ask_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (upper_ask_value, bytes) =>
                                  Some ({| instrument_id := instrument_id_value; collar_type := collar_type_value; price := price_value; lower_bid := lower_bid_value; upper_bid := upper_bid_value; lower_ask := lower_ask_value; upper_ask := upper_ask_value |}, bytes)
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

  End OrderCollars.

  Module TradeCollars.

    (** New trade price collars *)
    Record t := {
      instrument_id : N;
      collar_type : N;
      price : N;
      lower : N;
      upper : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (collar_type record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (lower record < 256 ^ N.of_nat 8)%N /\
      (upper record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (collar_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (lower record) ++
      encode_uint 8 (upper record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (collar_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (lower_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (upper_value, bytes) =>
                          Some ({| instrument_id := instrument_id_value; collar_type := collar_type_value; price := price_value; lower := lower_value; upper := upper_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
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

  End TradeCollars.

  Module InstrumentSummary.

    (** Provides brief instrument summary *)
    Record t := {
      instrument_id : N;
      last_traded_price : N;
      closing_price : N;
      closing_price_type : N;
      adjusted_closing_price : N;
      adjusted_closing_price_reason : N;
      pct_change : N;
      vwap : N;
      no_trades : N;
      total_volume : N;
      total_value : N;
      opening_price : N;
      max_price : N;
      min_price : N;
      is_correction : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (last_traded_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price_type record < 256 ^ N.of_nat 1)%N /\
      (adjusted_closing_price record < 256 ^ N.of_nat 8)%N /\
      (adjusted_closing_price_reason record < 256 ^ N.of_nat 1)%N /\
      (pct_change record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (no_trades record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      (total_value record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (max_price record < 256 ^ N.of_nat 8)%N /\
      (min_price record < 256 ^ N.of_nat 8)%N /\
      (is_correction record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (last_traded_price record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 1 (closing_price_type record) ++
      encode_uint 8 (adjusted_closing_price record) ++
      encode_uint 1 (adjusted_closing_price_reason record) ++
      encode_uint 8 (pct_change record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (no_trades record) ++
      encode_uint 8 (total_volume record) ++
      encode_uint 8 (total_value record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (max_price record) ++
      encode_uint 8 (min_price record) ++
      encode_uint 1 (is_correction record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (last_traded_price_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (closing_price_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (closing_price_type_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (adjusted_closing_price_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (adjusted_closing_price_reason_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (pct_change_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (vwap_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (no_trades_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (total_volume_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (total_value_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (opening_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (max_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (min_price_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (is_correction_value, bytes) =>
                                                                  Some ({| instrument_id := instrument_id_value; last_traded_price := last_traded_price_value; closing_price := closing_price_value; closing_price_type := closing_price_type_value; adjusted_closing_price := adjusted_closing_price_value; adjusted_closing_price_reason := adjusted_closing_price_reason_value; pct_change := pct_change_value; vwap := vwap_value; no_trades := no_trades_value; total_volume := total_volume_value; total_value := total_value_value; opening_price := opening_price_value; max_price := max_price_value; min_price := min_price_value; is_correction := is_correction_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 95.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End InstrumentSummary.

  Module ClobInstrument.

    (** SingleInstrumentSummary *)
    Record t := {
      instrument_id : N;
      market_model_type : N;
      last_traded_price : N;
      closing_price : N;
      closing_price_type : N;
      adjusted_closing_price : N;
      adjusted_closing_price_reason : N;
      pct_change : N;
      vwap : N;
      no_trades : N;
      total_volume : N;
      total_value : N;
      opening_price : N;
      max_price : N;
      min_price : N;
      settlement_price : N;
      settlement_value_price : N;
      end_trading_date : N;
      last_trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (market_model_type record < 256 ^ N.of_nat 1)%N /\
      (last_traded_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price_type record < 256 ^ N.of_nat 1)%N /\
      (adjusted_closing_price record < 256 ^ N.of_nat 8)%N /\
      (adjusted_closing_price_reason record < 256 ^ N.of_nat 1)%N /\
      (pct_change record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (no_trades record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      (total_value record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (max_price record < 256 ^ N.of_nat 8)%N /\
      (min_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_value_price record < 256 ^ N.of_nat 8)%N /\
      (end_trading_date record < 256 ^ N.of_nat 4)%N /\
      (last_trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (market_model_type record) ++
      encode_uint 8 (last_traded_price record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 1 (closing_price_type record) ++
      encode_uint 8 (adjusted_closing_price record) ++
      encode_uint 1 (adjusted_closing_price_reason record) ++
      encode_uint 8 (pct_change record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (no_trades record) ++
      encode_uint 8 (total_volume record) ++
      encode_uint 8 (total_value record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (max_price record) ++
      encode_uint 8 (min_price record) ++
      encode_uint 8 (settlement_price record) ++
      encode_uint 8 (settlement_value_price record) ++
      encode_uint 4 (end_trading_date record) ++
      encode_uint 4 (last_trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (market_model_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_traded_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (closing_price_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (closing_price_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (adjusted_closing_price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (adjusted_closing_price_reason_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (pct_change_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (vwap_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (no_trades_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (total_volume_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (total_value_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (opening_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (max_price_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (min_price_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (settlement_price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (settlement_value_price_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (end_trading_date_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (last_trade_date_value, bytes) =>
                                                                                  Some ({| instrument_id := instrument_id_value; market_model_type := market_model_type_value; last_traded_price := last_traded_price_value; closing_price := closing_price_value; closing_price_type := closing_price_type_value; adjusted_closing_price := adjusted_closing_price_value; adjusted_closing_price_reason := adjusted_closing_price_reason_value; pct_change := pct_change_value; vwap := vwap_value; no_trades := no_trades_value; total_volume := total_volume_value; total_value := total_value_value; opening_price := opening_price_value; max_price := max_price_value; min_price := min_price_value; settlement_price := settlement_price_value; settlement_value_price := settlement_value_price_value; end_trading_date := end_trading_date_value; last_trade_date := last_trade_date_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 119.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ClobInstrument.

  Module CrossInstrument.

    (** SingleInstrumentSummary *)
    Record t := {
      instrument_id : N;
      market_model_type : N;
      last_traded_price : N;
      closing_price : N;
      closing_price_type : N;
      adjusted_closing_price : N;
      adjusted_closing_price_reason : N;
      pct_change : N;
      vwap : N;
      no_trades : N;
      total_volume : N;
      total_value : N;
      opening_price : N;
      max_price : N;
      min_price : N;
      settlement_price : N;
      settlement_value_price : N;
      end_trading_date : N;
      last_trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (market_model_type record < 256 ^ N.of_nat 1)%N /\
      (last_traded_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price_type record < 256 ^ N.of_nat 1)%N /\
      (adjusted_closing_price record < 256 ^ N.of_nat 8)%N /\
      (adjusted_closing_price_reason record < 256 ^ N.of_nat 1)%N /\
      (pct_change record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (no_trades record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      (total_value record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (max_price record < 256 ^ N.of_nat 8)%N /\
      (min_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_value_price record < 256 ^ N.of_nat 8)%N /\
      (end_trading_date record < 256 ^ N.of_nat 4)%N /\
      (last_trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (market_model_type record) ++
      encode_uint 8 (last_traded_price record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 1 (closing_price_type record) ++
      encode_uint 8 (adjusted_closing_price record) ++
      encode_uint 1 (adjusted_closing_price_reason record) ++
      encode_uint 8 (pct_change record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (no_trades record) ++
      encode_uint 8 (total_volume record) ++
      encode_uint 8 (total_value record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (max_price record) ++
      encode_uint 8 (min_price record) ++
      encode_uint 8 (settlement_price record) ++
      encode_uint 8 (settlement_value_price record) ++
      encode_uint 4 (end_trading_date record) ++
      encode_uint 4 (last_trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (market_model_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_traded_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (closing_price_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (closing_price_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (adjusted_closing_price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (adjusted_closing_price_reason_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (pct_change_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (vwap_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (no_trades_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (total_volume_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (total_value_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (opening_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (max_price_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (min_price_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (settlement_price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (settlement_value_price_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (end_trading_date_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (last_trade_date_value, bytes) =>
                                                                                  Some ({| instrument_id := instrument_id_value; market_model_type := market_model_type_value; last_traded_price := last_traded_price_value; closing_price := closing_price_value; closing_price_type := closing_price_type_value; adjusted_closing_price := adjusted_closing_price_value; adjusted_closing_price_reason := adjusted_closing_price_reason_value; pct_change := pct_change_value; vwap := vwap_value; no_trades := no_trades_value; total_volume := total_volume_value; total_value := total_value_value; opening_price := opening_price_value; max_price := max_price_value; min_price := min_price_value; settlement_price := settlement_price_value; settlement_value_price := settlement_value_price_value; end_trading_date := end_trading_date_value; last_trade_date := last_trade_date_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 119.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End CrossInstrument.

  Module BlockInstrument.

    (** SingleInstrumentSummary *)
    Record t := {
      instrument_id : N;
      market_model_type : N;
      last_traded_price : N;
      closing_price : N;
      closing_price_type : N;
      adjusted_closing_price : N;
      adjusted_closing_price_reason : N;
      pct_change : N;
      vwap : N;
      no_trades : N;
      total_volume : N;
      total_value : N;
      opening_price : N;
      max_price : N;
      min_price : N;
      settlement_price : N;
      settlement_value_price : N;
      end_trading_date : N;
      last_trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (market_model_type record < 256 ^ N.of_nat 1)%N /\
      (last_traded_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price_type record < 256 ^ N.of_nat 1)%N /\
      (adjusted_closing_price record < 256 ^ N.of_nat 8)%N /\
      (adjusted_closing_price_reason record < 256 ^ N.of_nat 1)%N /\
      (pct_change record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (no_trades record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      (total_value record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (max_price record < 256 ^ N.of_nat 8)%N /\
      (min_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_value_price record < 256 ^ N.of_nat 8)%N /\
      (end_trading_date record < 256 ^ N.of_nat 4)%N /\
      (last_trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (market_model_type record) ++
      encode_uint 8 (last_traded_price record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 1 (closing_price_type record) ++
      encode_uint 8 (adjusted_closing_price record) ++
      encode_uint 1 (adjusted_closing_price_reason record) ++
      encode_uint 8 (pct_change record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (no_trades record) ++
      encode_uint 8 (total_volume record) ++
      encode_uint 8 (total_value record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (max_price record) ++
      encode_uint 8 (min_price record) ++
      encode_uint 8 (settlement_price record) ++
      encode_uint 8 (settlement_value_price record) ++
      encode_uint 4 (end_trading_date record) ++
      encode_uint 4 (last_trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (market_model_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_traded_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (closing_price_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (closing_price_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (adjusted_closing_price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (adjusted_closing_price_reason_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (pct_change_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (vwap_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (no_trades_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (total_volume_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (total_value_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (opening_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (max_price_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (min_price_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (settlement_price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (settlement_value_price_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (end_trading_date_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (last_trade_date_value, bytes) =>
                                                                                  Some ({| instrument_id := instrument_id_value; market_model_type := market_model_type_value; last_traded_price := last_traded_price_value; closing_price := closing_price_value; closing_price_type := closing_price_type_value; adjusted_closing_price := adjusted_closing_price_value; adjusted_closing_price_reason := adjusted_closing_price_reason_value; pct_change := pct_change_value; vwap := vwap_value; no_trades := no_trades_value; total_volume := total_volume_value; total_value := total_value_value; opening_price := opening_price_value; max_price := max_price_value; min_price := min_price_value; settlement_price := settlement_price_value; settlement_value_price := settlement_value_price_value; end_trading_date := end_trading_date_value; last_trade_date := last_trade_date_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 119.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BlockInstrument.

  Module HybridInstrument.

    (** SingleInstrumentSummary *)
    Record t := {
      instrument_id : N;
      market_model_type : N;
      last_traded_price : N;
      closing_price : N;
      closing_price_type : N;
      adjusted_closing_price : N;
      adjusted_closing_price_reason : N;
      pct_change : N;
      vwap : N;
      no_trades : N;
      total_volume : N;
      total_value : N;
      opening_price : N;
      max_price : N;
      min_price : N;
      settlement_price : N;
      settlement_value_price : N;
      end_trading_date : N;
      last_trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (market_model_type record < 256 ^ N.of_nat 1)%N /\
      (last_traded_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price_type record < 256 ^ N.of_nat 1)%N /\
      (adjusted_closing_price record < 256 ^ N.of_nat 8)%N /\
      (adjusted_closing_price_reason record < 256 ^ N.of_nat 1)%N /\
      (pct_change record < 256 ^ N.of_nat 8)%N /\
      (vwap record < 256 ^ N.of_nat 8)%N /\
      (no_trades record < 256 ^ N.of_nat 8)%N /\
      (total_volume record < 256 ^ N.of_nat 8)%N /\
      (total_value record < 256 ^ N.of_nat 8)%N /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (max_price record < 256 ^ N.of_nat 8)%N /\
      (min_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_price record < 256 ^ N.of_nat 8)%N /\
      (settlement_value_price record < 256 ^ N.of_nat 8)%N /\
      (end_trading_date record < 256 ^ N.of_nat 4)%N /\
      (last_trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (market_model_type record) ++
      encode_uint 8 (last_traded_price record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 1 (closing_price_type record) ++
      encode_uint 8 (adjusted_closing_price record) ++
      encode_uint 1 (adjusted_closing_price_reason record) ++
      encode_uint 8 (pct_change record) ++
      encode_uint 8 (vwap record) ++
      encode_uint 8 (no_trades record) ++
      encode_uint 8 (total_volume record) ++
      encode_uint 8 (total_value record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (max_price record) ++
      encode_uint 8 (min_price record) ++
      encode_uint 8 (settlement_price record) ++
      encode_uint 8 (settlement_value_price record) ++
      encode_uint 4 (end_trading_date record) ++
      encode_uint 4 (last_trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (market_model_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_traded_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (closing_price_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (closing_price_type_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (adjusted_closing_price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (adjusted_closing_price_reason_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (pct_change_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (vwap_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (no_trades_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (total_volume_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (total_value_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (opening_price_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (max_price_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (min_price_value, bytes) =>
                                                                  match decode_uint 8 bytes with
                                                                  | None => None
                                                                  | Some (settlement_price_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (settlement_value_price_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (end_trading_date_value, bytes) =>
                                                                              match decode_uint 4 bytes with
                                                                              | None => None
                                                                              | Some (last_trade_date_value, bytes) =>
                                                                                  Some ({| instrument_id := instrument_id_value; market_model_type := market_model_type_value; last_traded_price := last_traded_price_value; closing_price := closing_price_value; closing_price_type := closing_price_type_value; adjusted_closing_price := adjusted_closing_price_value; adjusted_closing_price_reason := adjusted_closing_price_reason_value; pct_change := pct_change_value; vwap := vwap_value; no_trades := no_trades_value; total_volume := total_volume_value; total_value := total_value_value; opening_price := opening_price_value; max_price := max_price_value; min_price := min_price_value; settlement_price := settlement_price_value; settlement_value_price := settlement_value_price_value; end_trading_date := end_trading_date_value; last_trade_date := last_trade_date_value |}, bytes)
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 119.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End HybridInstrument.

  Module ProductSummary.

    (** Session day product summary *)
    Record t := {
      clob_instrument : ClobInstrument.t;
      cross_instrument : CrossInstrument.t;
      block_instrument : BlockInstrument.t;
      hybrid_instrument : HybridInstrument.t;
      product_identification_type : N;
      product_identification_product_identification : list byte;
      product_id : N;
      mic : list byte;
      accumulated_interest : N;
      interest_rate : N;
      currency : N;
      session_date : N;
      trading_value_currency : N;
      status : N;
      sector : N;
      market : N;
      marker_price_change : N;
      lower_liquidity : N;
      multiplier_number : N;
      dividend_rate : N;
      delta : N;
      gamma : N;
      rho : N;
      theta : N;
      vega : N;
      volatility : N;
      options_strike_price : N;
      dividend : N;
      subscription_right : N;
      interim_dividend_right : N;
      split : N;
      quotation_system : N;
      liquidity_support_pge : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      ClobInstrument.bounded (clob_instrument record) /\
      CrossInstrument.bounded (cross_instrument record) /\
      BlockInstrument.bounded (block_instrument record) /\
      HybridInstrument.bounded (hybrid_instrument record) /\
      (product_identification_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (product_identification_product_identification record) = 30 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mic record) = 4 /\
      (accumulated_interest record < 256 ^ N.of_nat 8)%N /\
      (interest_rate record < 256 ^ N.of_nat 8)%N /\
      (currency record < 256 ^ N.of_nat 2)%N /\
      (session_date record < 256 ^ N.of_nat 4)%N /\
      (trading_value_currency record < 256 ^ N.of_nat 8)%N /\
      (status record < 256 ^ N.of_nat 1)%N /\
      (sector record < 256 ^ N.of_nat 2)%N /\
      (market record < 256 ^ N.of_nat 1)%N /\
      (marker_price_change record < 256 ^ N.of_nat 1)%N /\
      (lower_liquidity record < 256 ^ N.of_nat 1)%N /\
      (multiplier_number record < 256 ^ N.of_nat 8)%N /\
      (dividend_rate record < 256 ^ N.of_nat 8)%N /\
      (delta record < 256 ^ N.of_nat 8)%N /\
      (gamma record < 256 ^ N.of_nat 8)%N /\
      (rho record < 256 ^ N.of_nat 8)%N /\
      (theta record < 256 ^ N.of_nat 8)%N /\
      (vega record < 256 ^ N.of_nat 8)%N /\
      (volatility record < 256 ^ N.of_nat 8)%N /\
      (options_strike_price record < 256 ^ N.of_nat 8)%N /\
      (dividend record < 256 ^ N.of_nat 1)%N /\
      (subscription_right record < 256 ^ N.of_nat 1)%N /\
      (interim_dividend_right record < 256 ^ N.of_nat 1)%N /\
      (split record < 256 ^ N.of_nat 1)%N /\
      (quotation_system record < 256 ^ N.of_nat 1)%N /\
      (liquidity_support_pge record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      ClobInstrument.encode (clob_instrument record) ++
      CrossInstrument.encode (cross_instrument record) ++
      BlockInstrument.encode (block_instrument record) ++
      HybridInstrument.encode (hybrid_instrument record) ++
      encode_uint 1 (product_identification_type record) ++
      encode_bytes 30 (product_identification_product_identification record) ++
      encode_uint 4 (product_id record) ++
      encode_bytes 4 (mic record) ++
      encode_uint 8 (accumulated_interest record) ++
      encode_uint 8 (interest_rate record) ++
      encode_uint 2 (currency record) ++
      encode_uint 4 (session_date record) ++
      encode_uint 8 (trading_value_currency record) ++
      encode_uint 1 (status record) ++
      encode_uint 2 (sector record) ++
      encode_uint 1 (market record) ++
      encode_uint 1 (marker_price_change record) ++
      encode_uint 1 (lower_liquidity record) ++
      encode_uint 8 (multiplier_number record) ++
      encode_uint 8 (dividend_rate record) ++
      encode_uint 8 (delta record) ++
      encode_uint 8 (gamma record) ++
      encode_uint 8 (rho record) ++
      encode_uint 8 (theta record) ++
      encode_uint 8 (vega record) ++
      encode_uint 8 (volatility record) ++
      encode_uint 8 (options_strike_price record) ++
      encode_uint 1 (dividend record) ++
      encode_uint 1 (subscription_right record) ++
      encode_uint 1 (interim_dividend_right record) ++
      encode_uint 1 (split record) ++
      encode_uint 1 (quotation_system record) ++
      encode_uint 1 (liquidity_support_pge record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match ClobInstrument.decode bytes with
      | None => None
      | Some (clob_instrument_value, bytes) =>
          match CrossInstrument.decode bytes with
          | None => None
          | Some (cross_instrument_value, bytes) =>
              match BlockInstrument.decode bytes with
              | None => None
              | Some (block_instrument_value, bytes) =>
                  match HybridInstrument.decode bytes with
                  | None => None
                  | Some (hybrid_instrument_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (product_identification_type_value, bytes) =>
                          match decode_bytes 30 bytes with
                          | None => None
                          | Some (product_identification_product_identification_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (product_id_value, bytes) =>
                                  match decode_bytes 4 bytes with
                                  | None => None
                                  | Some (mic_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (accumulated_interest_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (interest_rate_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (currency_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (session_date_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (trading_value_currency_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (status_value, bytes) =>
                                                              match decode_uint 2 bytes with
                                                              | None => None
                                                              | Some (sector_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (market_value, bytes) =>
                                                                      match decode_uint 1 bytes with
                                                                      | None => None
                                                                      | Some (marker_price_change_value, bytes) =>
                                                                          match decode_uint 1 bytes with
                                                                          | None => None
                                                                          | Some (lower_liquidity_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (multiplier_number_value, bytes) =>
                                                                                  match decode_uint 8 bytes with
                                                                                  | None => None
                                                                                  | Some (dividend_rate_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (delta_value, bytes) =>
                                                                                          match decode_uint 8 bytes with
                                                                                          | None => None
                                                                                          | Some (gamma_value, bytes) =>
                                                                                              match decode_uint 8 bytes with
                                                                                              | None => None
                                                                                              | Some (rho_value, bytes) =>
                                                                                                  match decode_uint 8 bytes with
                                                                                                  | None => None
                                                                                                  | Some (theta_value, bytes) =>
                                                                                                      match decode_uint 8 bytes with
                                                                                                      | None => None
                                                                                                      | Some (vega_value, bytes) =>
                                                                                                          match decode_uint 8 bytes with
                                                                                                          | None => None
                                                                                                          | Some (volatility_value, bytes) =>
                                                                                                              match decode_uint 8 bytes with
                                                                                                              | None => None
                                                                                                              | Some (options_strike_price_value, bytes) =>
                                                                                                                  match decode_uint 1 bytes with
                                                                                                                  | None => None
                                                                                                                  | Some (dividend_value, bytes) =>
                                                                                                                      match decode_uint 1 bytes with
                                                                                                                      | None => None
                                                                                                                      | Some (subscription_right_value, bytes) =>
                                                                                                                          match decode_uint 1 bytes with
                                                                                                                          | None => None
                                                                                                                          | Some (interim_dividend_right_value, bytes) =>
                                                                                                                              match decode_uint 1 bytes with
                                                                                                                              | None => None
                                                                                                                              | Some (split_value, bytes) =>
                                                                                                                                  match decode_uint 1 bytes with
                                                                                                                                  | None => None
                                                                                                                                  | Some (quotation_system_value, bytes) =>
                                                                                                                                      match decode_uint 1 bytes with
                                                                                                                                      | None => None
                                                                                                                                      | Some (liquidity_support_pge_value, bytes) =>
                                                                                                                                          Some ({| clob_instrument := clob_instrument_value; cross_instrument := cross_instrument_value; block_instrument := block_instrument_value; hybrid_instrument := hybrid_instrument_value; product_identification_type := product_identification_type_value; product_identification_product_identification := product_identification_product_identification_value; product_id := product_id_value; mic := mic_value; accumulated_interest := accumulated_interest_value; interest_rate := interest_rate_value; currency := currency_value; session_date := session_date_value; trading_value_currency := trading_value_currency_value; status := status_value; sector := sector_value; market := market_value; marker_price_change := marker_price_change_value; lower_liquidity := lower_liquidity_value; multiplier_number := multiplier_number_value; dividend_rate := dividend_rate_value; delta := delta_value; gamma := gamma_value; rho := rho_value; theta := theta_value; vega := vega_value; volatility := volatility_value; options_strike_price := options_strike_price_value; dividend := dividend_value; subscription_right := subscription_right_value; interim_dividend_right := interim_dividend_right_value; split := split_value; quotation_system := quotation_system_value; liquidity_support_pge := liquidity_support_pge_value |}, bytes)
                                                                                                                                      end
                                                                                                                                  end
                                                                                                                              end
                                                                                                                          end
                                                                                                                      end
                                                                                                                  end
                                                                                                              end
                                                                                                          end
                                                                                                      end
                                                                                                  end
                                                                                              end
                                                                                          end
                                                                                      end
                                                                                  end
                                                                              end
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 629.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !ClobInstrument.encode_length, !CrossInstrument.encode_length, !BlockInstrument.encode_length, !HybridInstrument.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 [bound_25 [bound_26 [bound_27 [bound_28 [bound_29 [bound_30 [bound_31 bound_32]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite ClobInstrument.decode_encode by exact bound_0.
      rewrite CrossInstrument.decode_encode by exact bound_1.
      rewrite BlockInstrument.decode_encode by exact bound_2.
      rewrite HybridInstrument.decode_encode by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
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
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_uint by exact bound_23.
      rewrite decode_encode_uint by exact bound_24.
      rewrite decode_encode_uint by exact bound_25.
      rewrite decode_encode_uint by exact bound_26.
      rewrite decode_encode_uint by exact bound_27.
      rewrite decode_encode_uint by exact bound_28.
      rewrite decode_encode_uint by exact bound_29.
      rewrite decode_encode_uint by exact bound_30.
      rewrite decode_encode_uint by exact bound_31.
      rewrite decode_encode_uint by exact bound_32.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply ClobInstrument.eq_dec | apply CrossInstrument.eq_dec | apply BlockInstrument.eq_dec | apply HybridInstrument.eq_dec]. Defined.

  End ProductSummary.

  Module News.

    (** News message *)
    Record t := {
      market_structure_id : N;
      news_id : N;
      title : list byte;
      entry_number : N;
      total : N;
      text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (market_structure_id record < 256 ^ N.of_nat 4)%N /\
      (news_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (title record) = 80 /\
      (entry_number record < 256 ^ N.of_nat 1)%N /\
      (total record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (text record) = 800.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (market_structure_id record) ++
      encode_uint 4 (news_id record) ++
      encode_bytes 80 (title record) ++
      encode_uint 1 (entry_number record) ++
      encode_uint 1 (total record) ++
      encode_bytes 800 (text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (market_structure_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (news_id_value, bytes) =>
              match decode_bytes 80 bytes with
              | None => None
              | Some (title_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (entry_number_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (total_value, bytes) =>
                          match decode_bytes 800 bytes with
                          | None => None
                          | Some (text_value, bytes) =>
                              Some ({| market_structure_id := market_structure_id_value; news_id := news_id_value; title := title_value; entry_number := entry_number_value; total := total_value; text := text_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 890.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End News.

  Module TradingSessionStatus.

    (** The Trading Session Status provides information on the status of a market and on a trading day events *)
    Record t := {
      market_id : list byte;
      market_structure_id : N;
      trading_session_event : N;
      date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_id record) = 4 /\
      (market_structure_id record < 256 ^ N.of_nat 4)%N /\
      (trading_session_event record < 256 ^ N.of_nat 1)%N /\
      (date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (market_id record) ++
      encode_uint 4 (market_structure_id record) ++
      encode_uint 1 (trading_session_event record) ++
      encode_uint 4 (date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (market_structure_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (trading_session_event_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (date_value, bytes) =>
                      Some ({| market_id := market_id_value; market_structure_id := market_structure_id_value; trading_session_event := trading_session_event_value; date := date_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingSessionStatus.

  Module TestEvent.

    (** Test event *)
    Record t := {
      scenario_name : list byte;
      event_type_event_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (scenario_name record) = 200 /\
      (event_type_event_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 200 (scenario_name record) ++
      encode_uint 1 (event_type_event_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 200 bytes with
      | None => None
      | Some (scenario_name_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (event_type_event_type_value, bytes) =>
              Some ({| scenario_name := scenario_name_value; event_type_event_type := event_type_event_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 201.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TestEvent.

  Module OrderAdd.

    (** New (limit) order added to order book *)
    Record t := {
      public_order_id : N;
      instrument_id : N;
      side : N;
      price : N;
      quantity : N;
      mm_quote : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (public_order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (mm_quote record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (public_order_id record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 1 (mm_quote record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (public_order_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (mm_quote_value, bytes) =>
                              Some ({| public_order_id := public_order_id_value; instrument_id := instrument_id_value; side := side_value; price := price_value; quantity := quantity_value; mm_quote := mm_quote_value |}, bytes)
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

  End OrderAdd.

  Module OrderModify.

    (** Order modified *)
    Record t := {
      instrument_id : N;
      public_order_id : N;
      price : N;
      quantity : N;
      priority_flag : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (public_order_id record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (priority_flag record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (public_order_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 1 (priority_flag record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (public_order_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (priority_flag_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              Some ({| instrument_id := instrument_id_value; public_order_id := public_order_id_value; price := price_value; quantity := quantity_value; priority_flag := priority_flag_value; side := side_value |}, bytes)
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

  End OrderModify.

  Module OrderCancel.

    (** Order deleted *)
    Record t := {
      instrument_id : N;
      public_order_id : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (public_order_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (public_order_id record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (public_order_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  Some ({| instrument_id := instrument_id_value; public_order_id := public_order_id_value; side := side_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End OrderCancel.

  Module OrderExecute.

    (** Execution report *)
    Record t := {
      quantity : N;
      instrument_id : N;
      public_order_id : N;
      trade_id : N;
      execution_price : N;
      execution_quantity : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (public_order_id record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (execution_price record < 256 ^ N.of_nat 8)%N /\
      (execution_quantity record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (quantity record) ++
      encode_uint 4 (instrument_id record) ++
      encode_uint 8 (public_order_id record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 8 (execution_price record) ++
      encode_uint 8 (execution_quantity record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (quantity_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (public_order_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (execution_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (execution_quantity_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  Some ({| quantity := quantity_value; instrument_id := instrument_id_value; public_order_id := public_order_id_value; trade_id := trade_id_value; execution_price := execution_price_value; execution_quantity := execution_quantity_value; side := side_value |}, bytes)
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

  End OrderExecute.

  Module OrderBookEvent.

    (** Order book event for given instrument *)
    Record t := {
      instrument_id : N;
      event_type_order_book_event_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (event_type_order_book_event_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (instrument_id record) ++
      encode_uint 1 (event_type_order_book_event_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (event_type_order_book_event_type_value, bytes) =>
              Some ({| instrument_id := instrument_id_value; event_type_order_book_event_type := event_type_order_book_event_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
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

  End OrderBookEvent.

End WseReplayFullDepthV17620Tcp.
