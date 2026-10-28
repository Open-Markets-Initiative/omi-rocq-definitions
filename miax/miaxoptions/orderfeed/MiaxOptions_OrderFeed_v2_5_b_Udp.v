From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Miami International Holdings Order Feed

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
      - a length prefix framing what follows
      - a run counted by a field
  *)

Module MiaxOptionsOrderFeedV25BUdp.

  Module MachPacketHeader.

    (** Mach packet header (12 bytes) *)
    Record t := {
      sequence_number : N;
      packet_length : N;
      packet_type : N;
      session_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      (packet_type record < 256 ^ N.of_nat 1)%N /\
      (session_number record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (packet_length record) ++
      encode_uint 1 (packet_type record) ++
      encode_uint 1 (session_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (packet_length_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (packet_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_number_value, bytes) =>
                      Some ({| sequence_number := sequence_number_value; packet_length := packet_length_value; packet_type := packet_type_value; session_number := session_number_value |}, bytes)
                  end
              end
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

  End MachPacketHeader.

  Module SystemTimeMessage.

    (** This is the message format that will be used to disseminate the “seconds” part of the timestamp that is applicable to all messages that are sent in the current second. *)
    Record t := {
      seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          Some ({| seconds := seconds_value |}, bytes)
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

  End SystemTimeMessage.

  Module SimpleSeriesUpdateMessage.

    (** This is the message format that will be used to disseminate all Option series traded on MIAX for the current session. *)
    Record t := {
      nanoseconds : N;
      product_id : N;
      underlying_symbol : list byte;
      security_symbol : list byte;
      expiration_date : list byte;
      strike_price : N;
      call_or_put : list byte;
      opening_time : list byte;
      closing_time : list byte;
      restricted_option : list byte;
      long_term_option : list byte;
      active_on_miax : list byte;
      miax_bbo_posting_increment_indicator : list byte;
      liquidity_acceptance_increment_indicator : list byte;
      opening_underlying_market_code : list byte;
      priority_quote_width : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (security_symbol record) = 6 /\
      Datatypes.length (expiration_date record) = 8 /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (call_or_put record) = 1 /\
      Datatypes.length (opening_time record) = 8 /\
      Datatypes.length (closing_time record) = 8 /\
      Datatypes.length (restricted_option record) = 1 /\
      Datatypes.length (long_term_option record) = 1 /\
      Datatypes.length (active_on_miax record) = 1 /\
      Datatypes.length (miax_bbo_posting_increment_indicator record) = 1 /\
      Datatypes.length (liquidity_acceptance_increment_indicator record) = 1 /\
      Datatypes.length (opening_underlying_market_code record) = 1 /\
      (priority_quote_width record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_uint 4 (product_id record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 6 (security_symbol record) ++
      encode_bytes 8 (expiration_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 1 (call_or_put record) ++
      encode_bytes 8 (opening_time record) ++
      encode_bytes 8 (closing_time record) ++
      encode_bytes 1 (restricted_option record) ++
      encode_bytes 1 (long_term_option record) ++
      encode_bytes 1 (active_on_miax record) ++
      encode_bytes 1 (miax_bbo_posting_increment_indicator record) ++
      encode_bytes 1 (liquidity_acceptance_increment_indicator record) ++
      encode_bytes 1 (opening_underlying_market_code record) ++
      encode_uint 4 (priority_quote_width record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (product_id_value, bytes) =>
              match decode_bytes 11 bytes with
              | None => None
              | Some (underlying_symbol_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (security_symbol_value, bytes) =>
                      match decode_bytes 8 bytes with
                      | None => None
                      | Some (expiration_date_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (call_or_put_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (opening_time_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (closing_time_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (restricted_option_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (long_term_option_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (active_on_miax_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (miax_bbo_posting_increment_indicator_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (liquidity_acceptance_increment_indicator_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (opening_underlying_market_code_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (priority_quote_width_value, bytes) =>
                                                                      match decode_uint 8 bytes with
                                                                      | None => None
                                                                      | Some (reserved_8_value, bytes) =>
                                                                          Some ({| nanoseconds := nanoseconds_value; product_id := product_id_value; underlying_symbol := underlying_symbol_value; security_symbol := security_symbol_value; expiration_date := expiration_date_value; strike_price := strike_price_value; call_or_put := call_or_put_value; opening_time := opening_time_value; closing_time := closing_time_value; restricted_option := restricted_option_value; long_term_option := long_term_option_value; active_on_miax := active_on_miax_value; miax_bbo_posting_increment_indicator := miax_bbo_posting_increment_indicator_value; liquidity_acceptance_increment_indicator := liquidity_acceptance_increment_indicator_value; opening_underlying_market_code := opening_underlying_market_code_value; priority_quote_width := priority_quote_width_value; reserved_8 := reserved_8_value |}, bytes)
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 72.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
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
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleSeriesUpdateMessage.

  Module SystemStateMessage.

    (** This message format is used to notify the firms of the state changes of the system. This is a notification that applies to each Underlying group. Firms can use notifications as triggers in their system to ensure electronic synchronization of systems. *)
    Record t := {
      nanoseconds : N;
      mor_version : list byte;
      session_id : N;
      system_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (mor_version record) = 8 /\
      (session_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (system_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 8 (mor_version record) ++
      encode_uint 4 (session_id record) ++
      encode_bytes 1 (system_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (mor_version_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (session_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (system_status_value, bytes) =>
                      Some ({| nanoseconds := nanoseconds_value; mor_version := mor_version_value; session_id := session_id_value; system_status := system_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End SystemStateMessage.

  Module UnderlyingTradingStatusNotificationMessage.

    (** This message format will be used to notify firms of changes to the trading status of all the options of an underlying. *)
    Record t := {
      nanoseconds : N;
      underlying_symbol : list byte;
      trading_status : list byte;
      event_reason : list byte;
      expected_event_time_seconds_part : N;
      expected_event_time_nano_seconds_part : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying_symbol record) = 11 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (event_reason record) = 1 /\
      (expected_event_time_seconds_part record < 256 ^ N.of_nat 4)%N /\
      (expected_event_time_nano_seconds_part record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 11 (underlying_symbol record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 1 (event_reason record) ++
      encode_uint 4 (expected_event_time_seconds_part record) ++
      encode_uint 4 (expected_event_time_nano_seconds_part record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 11 bytes with
          | None => None
          | Some (underlying_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (event_reason_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (expected_event_time_seconds_part_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (expected_event_time_nano_seconds_part_value, bytes) =>
                              Some ({| nanoseconds := nanoseconds_value; underlying_symbol := underlying_symbol_value; trading_status := trading_status_value; event_reason := event_reason_value; expected_event_time_seconds_part := expected_event_time_seconds_part_value; expected_event_time_nano_seconds_part := expected_event_time_nano_seconds_part_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingTradingStatusNotificationMessage.

  Module SimpleOrderMessage.

    (** This is the message format that will be used to disseminate MIAX Options Simple Orders. *)
    Record t := {
      nanoseconds : N;
      action : list byte;
      product_id : N;
      order_id : N;
      order_side : list byte;
      order_type : list byte;
      order_price_short : N;
      order_original_volume : N;
      remaining_volume_open : N;
      time_in_force_tif : list byte;
      origin : list byte;
      openclose_indicator : list byte;
      route_instruction : list byte;
      attributed_id : list byte;
      priority_customer_volume : N;
      reserved_28 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (action record) = 1 /\
      (product_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_side record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      (order_price_short record < 256 ^ N.of_nat 4)%N /\
      (order_original_volume record < 256 ^ N.of_nat 4)%N /\
      (remaining_volume_open record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time_in_force_tif record) = 1 /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (openclose_indicator record) = 1 /\
      Datatypes.length (route_instruction record) = 1 /\
      Datatypes.length (attributed_id record) = 4 /\
      (priority_customer_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reserved_28 record) = 28.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (action record) ++
      encode_uint 4 (product_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (order_side record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 4 (order_price_short record) ++
      encode_uint 4 (order_original_volume record) ++
      encode_uint 4 (remaining_volume_open record) ++
      encode_bytes 1 (time_in_force_tif record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 1 (openclose_indicator record) ++
      encode_bytes 1 (route_instruction record) ++
      encode_bytes 4 (attributed_id record) ++
      encode_uint 4 (priority_customer_volume record) ++
      encode_bytes 28 (reserved_28 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (action_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (product_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (order_side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (order_type_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (order_price_short_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_original_volume_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (remaining_volume_open_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (time_in_force_tif_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (origin_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (openclose_indicator_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (route_instruction_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (attributed_id_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (priority_customer_volume_value, bytes) =>
                                                                  match decode_bytes 28 bytes with
                                                                  | None => None
                                                                  | Some (reserved_28_value, bytes) =>
                                                                      Some ({| nanoseconds := nanoseconds_value; action := action_value; product_id := product_id_value; order_id := order_id_value; order_side := order_side_value; order_type := order_type_value; order_price_short := order_price_short_value; order_original_volume := order_original_volume_value; remaining_volume_open := remaining_volume_open_value; time_in_force_tif := time_in_force_tif_value; origin := origin_value; openclose_indicator := openclose_indicator_value; route_instruction := route_instruction_value; attributed_id := attributed_id_value; priority_customer_volume := priority_customer_volume_value; reserved_28 := reserved_28_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SimpleOrderMessage.

  Module ComplexOrderMessage.

    (** This is the message format that will be used to disseminate MIAX Options Complex Orders. *)
    Record t := {
      nanoseconds : N;
      action : list byte;
      strategy_id : N;
      order_id : N;
      order_side : list byte;
      order_type : list byte;
      order_price_long : N;
      order_original_volume : N;
      remaining_volume_open : N;
      time_in_force_tif : list byte;
      origin : list byte;
      attributed_id : list byte;
      reserved_28 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (action record) = 1 /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_side record) = 1 /\
      Datatypes.length (order_type record) = 1 /\
      (order_price_long record < 256 ^ N.of_nat 8)%N /\
      (order_original_volume record < 256 ^ N.of_nat 4)%N /\
      (remaining_volume_open record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (time_in_force_tif record) = 1 /\
      Datatypes.length (origin record) = 1 /\
      Datatypes.length (attributed_id record) = 4 /\
      Datatypes.length (reserved_28 record) = 28.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (action record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (order_id record) ++
      encode_bytes 1 (order_side record) ++
      encode_bytes 1 (order_type record) ++
      encode_uint 8 (order_price_long record) ++
      encode_uint 4 (order_original_volume record) ++
      encode_uint 4 (remaining_volume_open record) ++
      encode_bytes 1 (time_in_force_tif record) ++
      encode_bytes 1 (origin record) ++
      encode_bytes 4 (attributed_id record) ++
      encode_bytes 28 (reserved_28 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (action_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (strategy_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_id_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (order_side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (order_type_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (order_price_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (order_original_volume_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (remaining_volume_open_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (time_in_force_tif_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (origin_value, bytes) =>
                                                  match decode_bytes 4 bytes with
                                                  | None => None
                                                  | Some (attributed_id_value, bytes) =>
                                                      match decode_bytes 28 bytes with
                                                      | None => None
                                                      | Some (reserved_28_value, bytes) =>
                                                          Some ({| nanoseconds := nanoseconds_value; action := action_value; strategy_id := strategy_id_value; order_id := order_id_value; order_side := order_side_value; order_type := order_type_value; order_price_long := order_price_long_value; order_original_volume := order_original_volume_value; remaining_volume_open := remaining_volume_open_value; time_in_force_tif := time_in_force_tif_value; origin := origin_value; attributed_id := attributed_id_value; reserved_28 := reserved_28_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 69.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
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

  End ComplexOrderMessage.

  Module OrderCloseMessage.

    (** This is the message format that will be used to disseminate Order Close for MIAX Options Simple and Complex Orders. *)
    Record t := {
      nanoseconds : N;
      simple_or_complex_order : list byte;
      order_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanoseconds record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (simple_or_complex_order record) = 1 /\
      (order_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (nanoseconds record) ++
      encode_bytes 1 (simple_or_complex_order record) ++
      encode_uint 8 (order_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (nanoseconds_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (simple_or_complex_order_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (order_id_value, bytes) =>
                  Some ({| nanoseconds := nanoseconds_value; simple_or_complex_order := simple_or_complex_order_value; order_id := order_id_value |}, bytes)
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

  End OrderCloseMessage.

End MiaxOptionsOrderFeedV25BUdp.
