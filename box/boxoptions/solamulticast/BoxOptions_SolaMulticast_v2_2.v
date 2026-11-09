From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Box Options Market Sola Multicast

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
      - a Composite rule
      - a run counted by a field

    License: MIT No Attribution
  *)

Module BoxOptionsSolaMulticastV22.

  Module MessageHeader.

    (** Hsvf Udp Market Data Packet Header *)
    Record t := {
      sequence_number : list byte;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sequence_number record) = 9 /\
      Datatypes.length (message_type record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (sequence_number record) ++
      encode_bytes 2 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module EndOfTransmissionMessage.

    (** This message will be sent to indicate that the day's transmission is complete *)
    Record t := {
      exchange_id : list byte;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_value, bytes) =>
              Some ({| exchange_id := exchange_id_value; time := time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfTransmissionMessage.

  Module CircuitAssuranceMessage.

    (** This message is sent out if no messages are sent by BOX for more than one second after the broadcast has started *)
    Record t := {
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (time_value, bytes) =>
          Some ({| time := time_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
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

  End CircuitAssuranceMessage.

  Module SystemTimestampMessage.

    (** This message is sent out every second and contains the time stamp when it was originally transmitted by the trading engine *)
    Record t := {
      trading_engine_timestamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_engine_timestamp record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (trading_engine_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (trading_engine_timestamp_value, bytes) =>
          Some ({| trading_engine_timestamp := trading_engine_timestamp_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End SystemTimestampMessage.

  Module InstrumentDescription.

    Record t := {
      root_symbol : list byte;
      expiry_month_code : list byte;
      filler_1 : N;
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
      expiry_year : list byte;
      expiry_day : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (root_symbol record) = 6 /\
      Datatypes.length (expiry_month_code record) = 1 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1 /\
      Datatypes.length (expiry_year record) = 2 /\
      Datatypes.length (expiry_day record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (root_symbol record) ++
      encode_bytes 1 (expiry_month_code record) ++
      encode_uint 1 (filler_1 record) ++
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record) ++
      encode_bytes 2 (expiry_year record) ++
      encode_bytes 2 (expiry_day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (root_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (expiry_month_code_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (filler_1_value, bytes) =>
                  match decode_bytes 7 bytes with
                  | None => None
                  | Some (strike_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (strike_price_fraction_indicator_value, bytes) =>
                          match decode_bytes 2 bytes with
                          | None => None
                          | Some (expiry_year_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (expiry_day_value, bytes) =>
                                  Some ({| root_symbol := root_symbol_value; expiry_month_code := expiry_month_code_value; filler_1 := filler_1_value; strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value; expiry_year := expiry_year_value; expiry_day := expiry_day_value |}, bytes)
                              end
                          end
                      end
                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentDescription.

  Module GroupOpeningTimeMessage.

    (** Group Opening Time *)
    Record t := {
      exchange_id : list byte;
      root_symbol : list byte;
      group_status : list byte;
      scheduled_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (root_symbol record) = 6 /\
      Datatypes.length (group_status record) = 1 /\
      Datatypes.length (scheduled_time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (root_symbol record) ++
      encode_bytes 1 (group_status record) ++
      encode_bytes 6 (scheduled_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (root_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (group_status_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (scheduled_time_value, bytes) =>
                      Some ({| exchange_id := exchange_id_value; root_symbol := root_symbol_value; group_status := group_status_value; scheduled_time := scheduled_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End GroupOpeningTimeMessage.

  Module GroupStatusMessage.

    (** This message will be sent when a group of trading instruments enters a new status *)
    Record t := {
      exchange_id : list byte;
      root_symbol : list byte;
      group_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (root_symbol record) = 6 /\
      Datatypes.length (group_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (root_symbol record) ++
      encode_bytes 1 (group_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (root_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (group_status_value, bytes) =>
                  Some ({| exchange_id := exchange_id_value; root_symbol := root_symbol_value; group_status := group_status_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GroupStatusMessage.

  Module StrategiesGroupStatusMessage.

    (** This message will be sent when a group of complex trading instruments enters a new status *)
    Record t := {
      exchange_id : list byte;
      group_of_the_complex_order_instrument : list byte;
      group_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (group_of_the_complex_order_instrument record) = 2 /\
      Datatypes.length (group_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 2 (group_of_the_complex_order_instrument record) ++
      encode_bytes 1 (group_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_of_the_complex_order_instrument_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (group_status_value, bytes) =>
                  Some ({| exchange_id := exchange_id_value; group_of_the_complex_order_instrument := group_of_the_complex_order_instrument_value; group_status := group_status_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategiesGroupStatusMessage.

  Module MarketFlowIndicator.

    Record t := {
      type_of_instrument : list byte;
      type_of_underlying : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (type_of_instrument record) = 1 /\
      Datatypes.length (type_of_underlying record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (type_of_instrument record) ++
      encode_bytes 1 (type_of_underlying record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (type_of_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (type_of_underlying_value, bytes) =>
              Some ({| type_of_instrument := type_of_instrument_value; type_of_underlying := type_of_underlying_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketFlowIndicator.

  Module OptionMarker.

    Record t := {
      type_of_market : list byte;
      type_of_options : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (type_of_market record) = 1 /\
      Datatypes.length (type_of_options record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (type_of_market record) ++
      encode_bytes 1 (type_of_options record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (type_of_market_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (type_of_options_value, bytes) =>
              Some ({| type_of_market := type_of_market_value; type_of_options := type_of_options_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionMarker.

  Module OptionInstrumentKeysMessage.

    (** Option Instrument Keys *)
    Record t := {
      exchange_id : list byte;
      instrument_description : InstrumentDescription.t;
      strike_price_currency : list byte;
      maximum_number_of_contracts_per_order : list byte;
      minimum_number_of_contracts_per_order : list byte;
      maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
      minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
      tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
      option_type : list byte;
      market_flow_indicator : MarketFlowIndicator.t;
      group_instrument : list byte;
      instrument : list byte;
      instrument_external_code : list byte;
      option_marker : OptionMarker.t;
      underlying_symbol_root : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      InstrumentDescription.bounded (instrument_description record) /\
      Datatypes.length (strike_price_currency record) = 3 /\
      Datatypes.length (maximum_number_of_contracts_per_order record) = 6 /\
      Datatypes.length (minimum_number_of_contracts_per_order record) = 6 /\
      Datatypes.length (maximum_threshold_price record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1 /\
      Datatypes.length (minimum_threshold_price record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1 /\
      Datatypes.length (tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1 /\
      Datatypes.length (option_type record) = 1 /\
      MarketFlowIndicator.bounded (market_flow_indicator record) /\
      Datatypes.length (group_instrument record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (instrument_external_code record) = 30 /\
      OptionMarker.bounded (option_marker record) /\
      Datatypes.length (underlying_symbol_root record) = 10.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      InstrumentDescription.encode (instrument_description record) ++
      encode_bytes 3 (strike_price_currency record) ++
      encode_bytes 6 (maximum_number_of_contracts_per_order record) ++
      encode_bytes 6 (minimum_number_of_contracts_per_order record) ++
      encode_bytes 6 (maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record) ++
      encode_bytes 6 (minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record) ++
      encode_bytes 6 (tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record) ++
      encode_bytes 1 (option_type record) ++
      MarketFlowIndicator.encode (market_flow_indicator record) ++
      encode_bytes 2 (group_instrument record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 30 (instrument_external_code record) ++
      OptionMarker.encode (option_marker record) ++
      encode_bytes 10 (underlying_symbol_root record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match InstrumentDescription.decode bytes with
          | None => None
          | Some (instrument_description_value, bytes) =>
              match decode_bytes 3 bytes with
              | None => None
              | Some (strike_price_currency_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (maximum_number_of_contracts_per_order_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (minimum_number_of_contracts_per_order_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (maximum_threshold_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (minimum_threshold_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (tick_increment_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (tick_increment_fraction_indicator_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (option_type_value, bytes) =>
                                                      match MarketFlowIndicator.decode bytes with
                                                      | None => None
                                                      | Some (market_flow_indicator_value, bytes) =>
                                                          match decode_bytes 2 bytes with
                                                          | None => None
                                                          | Some (group_instrument_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (instrument_value, bytes) =>
                                                                  match decode_bytes 30 bytes with
                                                                  | None => None
                                                                  | Some (instrument_external_code_value, bytes) =>
                                                                      match OptionMarker.decode bytes with
                                                                      | None => None
                                                                      | Some (option_marker_value, bytes) =>
                                                                          match decode_bytes 10 bytes with
                                                                          | None => None
                                                                          | Some (underlying_symbol_root_value, bytes) =>
                                                                              Some ({| exchange_id := exchange_id_value; instrument_description := instrument_description_value; strike_price_currency := strike_price_currency_value; maximum_number_of_contracts_per_order := maximum_number_of_contracts_per_order_value; minimum_number_of_contracts_per_order := minimum_number_of_contracts_per_order_value; maximum_threshold_price := maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value; minimum_threshold_price := minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value; tick_increment := tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value; option_type := option_type_value; market_flow_indicator := market_flow_indicator_value; group_instrument := group_instrument_value; instrument := instrument_value; instrument_external_code := instrument_external_code_value; option_marker := option_marker_value; underlying_symbol_root := underlying_symbol_root_value |}, bytes)
                                                                          end
                                                                      end
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 108.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !InstrumentDescription.encode_length, !MarketFlowIndicator.encode_length, !OptionMarker.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite InstrumentDescription.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite MarketFlowIndicator.decode_encode by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite OptionMarker.decode_encode by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InstrumentDescription.eq_dec | apply MarketFlowIndicator.eq_dec | apply OptionMarker.eq_dec]. Defined.

  End OptionInstrumentKeysMessage.

  Module BeginningOfOptionsSummaryMessage.

    (** This message indicates that the beginning and the end of day option summaries *)
    Record t := {
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          Some ({| exchange_id := exchange_id_value |}, bytes)
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

  End BeginningOfOptionsSummaryMessage.

  Module BeginningOfComplexOrderSummaryMessage.

    (** This message indicates that the beginning and the end of day Complex Order summaries *)
    Record t := {
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          Some ({| exchange_id := exchange_id_value |}, bytes)
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

  End BeginningOfComplexOrderSummaryMessage.

  Module EndOfSalesMessage.

    (** This message is sent when there is no more trading activity to be transmitted *)
    Record t := {
      reserved : N;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (reserved record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (reserved_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_value, bytes) =>
              Some ({| reserved := reserved_value; time := time_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfSalesMessage.

  Module StartOfAuctionOnOptionMessage.

    (** Start of Auction on Option *)
    Record t := {
      exchange_id : list byte;
      instrument_description : InstrumentDescription.t;
      improvement_phase_sequential_number : list byte;
      initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
      initial_order_quantity : list byte;
      initial_order_side : list byte;
      improvement_phase_expiry_time : list byte;
      filler_4 : N;
      minimum_quantity_for_improvement_order : list byte;
      percentage_assured_to_initial_order : list byte;
      auction_type : list byte;
      filler_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      InstrumentDescription.bounded (instrument_description record) /\
      Datatypes.length (improvement_phase_sequential_number record) = 6 /\
      Datatypes.length (initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1 /\
      Datatypes.length (initial_order_quantity record) = 8 /\
      Datatypes.length (initial_order_side record) = 1 /\
      Datatypes.length (improvement_phase_expiry_time record) = 8 /\
      (filler_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (minimum_quantity_for_improvement_order record) = 8 /\
      Datatypes.length (percentage_assured_to_initial_order record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      InstrumentDescription.encode (instrument_description record) ++
      encode_bytes 6 (improvement_phase_sequential_number record) ++
      encode_bytes 6 (initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record) ++
      encode_bytes 8 (initial_order_quantity record) ++
      encode_bytes 1 (initial_order_side record) ++
      encode_bytes 8 (improvement_phase_expiry_time record) ++
      encode_uint 4 (filler_4 record) ++
      encode_bytes 8 (minimum_quantity_for_improvement_order record) ++
      encode_bytes 8 (percentage_assured_to_initial_order record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 1 (filler_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match InstrumentDescription.decode bytes with
          | None => None
          | Some (instrument_description_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (improvement_phase_sequential_number_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (initial_order_price_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (initial_order_price_fraction_indicator_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (initial_order_quantity_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (initial_order_side_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (improvement_phase_expiry_time_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (filler_4_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (minimum_quantity_for_improvement_order_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (percentage_assured_to_initial_order_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (auction_type_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (filler_1_value, bytes) =>
                                                          Some ({| exchange_id := exchange_id_value; instrument_description := instrument_description_value; improvement_phase_sequential_number := improvement_phase_sequential_number_value; initial_order_price := initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value; initial_order_quantity := initial_order_quantity_value; initial_order_side := initial_order_side_value; improvement_phase_expiry_time := improvement_phase_expiry_time_value; filler_4 := filler_4_value; minimum_quantity_for_improvement_order := minimum_quantity_for_improvement_order_value; percentage_assured_to_initial_order := percentage_assured_to_initial_order_value; auction_type := auction_type_value; filler_1 := filler_1_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !InstrumentDescription.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite InstrumentDescription.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InstrumentDescription.eq_dec]. Defined.

  End StartOfAuctionOnOptionMessage.

  Module StartOfAuctionOnComplexOrderMessage.

    (** Start of Auction on Complex Order *)
    Record t := {
      exchange_id : list byte;
      complex_order_instrument_symbol : list byte;
      improvement_phase_sequential_number : list byte;
      initial_order_price_sign : list byte;
      initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
      initial_order_quantity : list byte;
      initial_order_side : list byte;
      improvement_phase_expiry_time : list byte;
      filler_4 : N;
      minimum_quantity_for_improvement_order : list byte;
      percentage_assured_to_initial_order : list byte;
      auction_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (complex_order_instrument_symbol record) = 30 /\
      Datatypes.length (improvement_phase_sequential_number record) = 6 /\
      Datatypes.length (initial_order_price_sign record) = 1 /\
      Datatypes.length (initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1 /\
      Datatypes.length (initial_order_quantity record) = 8 /\
      Datatypes.length (initial_order_side record) = 1 /\
      Datatypes.length (improvement_phase_expiry_time record) = 8 /\
      (filler_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (minimum_quantity_for_improvement_order record) = 8 /\
      Datatypes.length (percentage_assured_to_initial_order record) = 8 /\
      Datatypes.length (auction_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (complex_order_instrument_symbol record) ++
      encode_bytes 6 (improvement_phase_sequential_number record) ++
      encode_bytes 1 (initial_order_price_sign record) ++
      encode_bytes 6 (initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record) ++
      encode_bytes 8 (initial_order_quantity record) ++
      encode_bytes 1 (initial_order_side record) ++
      encode_bytes 8 (improvement_phase_expiry_time record) ++
      encode_uint 4 (filler_4 record) ++
      encode_bytes 8 (minimum_quantity_for_improvement_order record) ++
      encode_bytes 8 (percentage_assured_to_initial_order record) ++
      encode_bytes 1 (auction_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (complex_order_instrument_symbol_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (improvement_phase_sequential_number_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (initial_order_price_sign_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (initial_order_price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (initial_order_price_fraction_indicator_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (initial_order_quantity_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (initial_order_side_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (improvement_phase_expiry_time_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (filler_4_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (minimum_quantity_for_improvement_order_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (percentage_assured_to_initial_order_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (auction_type_value, bytes) =>
                                                          Some ({| exchange_id := exchange_id_value; complex_order_instrument_symbol := complex_order_instrument_symbol_value; improvement_phase_sequential_number := improvement_phase_sequential_number_value; initial_order_price_sign := initial_order_price_sign_value; initial_order_price := initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value; initial_order_quantity := initial_order_quantity_value; initial_order_side := initial_order_side_value; improvement_phase_expiry_time := improvement_phase_expiry_time_value; filler_4 := filler_4_value; minimum_quantity_for_improvement_order := minimum_quantity_for_improvement_order_value; percentage_assured_to_initial_order := percentage_assured_to_initial_order_value; auction_type := auction_type_value |}, bytes)
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 83.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StartOfAuctionOnComplexOrderMessage.

  Module StartOfExpositionOnOptionMessage.

    (** Start of Exposition on Option *)
    Record t := {
      exchange_id : list byte;
      instrument_description : InstrumentDescription.t;
      order_side : list byte;
      type_of_order : list byte;
      limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
      order_quantity : list byte;
      order_sequence_number : list byte;
      filler_6 : N;
      type_of_clearing_account : list byte;
      filler_1 : N;
      end_of_the_exposition : list byte;
      auction_type : list byte;
      firm_id : list byte;
      cmta : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      InstrumentDescription.bounded (instrument_description record) /\
      Datatypes.length (order_side record) = 1 /\
      Datatypes.length (type_of_order record) = 1 /\
      Datatypes.length (limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1 /\
      Datatypes.length (order_quantity record) = 8 /\
      Datatypes.length (order_sequence_number record) = 6 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (type_of_clearing_account record) = 1 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (end_of_the_exposition record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cmta record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      InstrumentDescription.encode (instrument_description record) ++
      encode_bytes 1 (order_side record) ++
      encode_bytes 1 (type_of_order record) ++
      encode_bytes 6 (limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record) ++
      encode_bytes 8 (order_quantity record) ++
      encode_bytes 6 (order_sequence_number record) ++
      encode_uint 6 (filler_6 record) ++
      encode_bytes 1 (type_of_clearing_account record) ++
      encode_uint 1 (filler_1 record) ++
      encode_bytes 8 (end_of_the_exposition record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 4 (firm_id record) ++
      encode_bytes 4 (cmta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match InstrumentDescription.decode bytes with
          | None => None
          | Some (instrument_description_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_side_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (type_of_order_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (limit_entered_for_an_order_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (limit_fraction_indicator_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (order_quantity_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (order_sequence_number_value, bytes) =>
                                      match decode_uint 6 bytes with
                                      | None => None
                                      | Some (filler_6_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (type_of_clearing_account_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (filler_1_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (end_of_the_exposition_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (auction_type_value, bytes) =>
                                                          match decode_bytes 4 bytes with
                                                          | None => None
                                                          | Some (firm_id_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (cmta_value, bytes) =>
                                                                  Some ({| exchange_id := exchange_id_value; instrument_description := instrument_description_value; order_side := order_side_value; type_of_order := type_of_order_value; limit_entered_for_an_order := limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value; order_quantity := order_quantity_value; order_sequence_number := order_sequence_number_value; filler_6 := filler_6_value; type_of_clearing_account := type_of_clearing_account_value; filler_1 := filler_1_value; end_of_the_exposition := end_of_the_exposition_value; auction_type := auction_type_value; firm_id := firm_id_value; cmta := cmta_value |}, bytes)
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !InstrumentDescription.encode_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite InstrumentDescription.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InstrumentDescription.eq_dec]. Defined.

  End StartOfExpositionOnOptionMessage.

  Module StartOfExpositionOnComplexOrderMessage.

    (** Start of Exposition on Complex Order *)
    Record t := {
      exchange_id : list byte;
      complex_order_instrument_symbol : list byte;
      order_side : list byte;
      type_of_order : list byte;
      limit_entered_for_an_order_sign : list byte;
      limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
      order_quantity : list byte;
      order_sequence_number : list byte;
      filler_6 : N;
      type_of_clearing_account : list byte;
      filler_1 : N;
      end_of_the_exposition : list byte;
      auction_type : list byte;
      firm_id : list byte;
      cmta : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (complex_order_instrument_symbol record) = 30 /\
      Datatypes.length (order_side record) = 1 /\
      Datatypes.length (type_of_order record) = 1 /\
      Datatypes.length (limit_entered_for_an_order_sign record) = 1 /\
      Datatypes.length (limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1 /\
      Datatypes.length (order_quantity record) = 8 /\
      Datatypes.length (order_sequence_number record) = 6 /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (type_of_clearing_account record) = 1 /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (end_of_the_exposition record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (firm_id record) = 4 /\
      Datatypes.length (cmta record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (complex_order_instrument_symbol record) ++
      encode_bytes 1 (order_side record) ++
      encode_bytes 1 (type_of_order record) ++
      encode_bytes 1 (limit_entered_for_an_order_sign record) ++
      encode_bytes 6 (limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record) ++
      encode_bytes 8 (order_quantity record) ++
      encode_bytes 6 (order_sequence_number record) ++
      encode_uint 6 (filler_6 record) ++
      encode_bytes 1 (type_of_clearing_account record) ++
      encode_uint 1 (filler_1 record) ++
      encode_bytes 8 (end_of_the_exposition record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 4 (firm_id record) ++
      encode_bytes 4 (cmta record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (complex_order_instrument_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_side_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (type_of_order_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (limit_entered_for_an_order_sign_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (limit_entered_for_an_order_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (limit_fraction_indicator_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (order_quantity_value, bytes) =>
                                      match decode_bytes 6 bytes with
                                      | None => None
                                      | Some (order_sequence_number_value, bytes) =>
                                          match decode_uint 6 bytes with
                                          | None => None
                                          | Some (filler_6_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (type_of_clearing_account_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (filler_1_value, bytes) =>
                                                      match decode_bytes 8 bytes with
                                                      | None => None
                                                      | Some (end_of_the_exposition_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (auction_type_value, bytes) =>
                                                              match decode_bytes 4 bytes with
                                                              | None => None
                                                              | Some (firm_id_value, bytes) =>
                                                                  match decode_bytes 4 bytes with
                                                                  | None => None
                                                                  | Some (cmta_value, bytes) =>
                                                                      Some ({| exchange_id := exchange_id_value; complex_order_instrument_symbol := complex_order_instrument_symbol_value; order_side := order_side_value; type_of_order := type_of_order_value; limit_entered_for_an_order_sign := limit_entered_for_an_order_sign_value; limit_entered_for_an_order := limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value; order_quantity := order_quantity_value; order_sequence_number := order_sequence_number_value; filler_6 := filler_6_value; type_of_clearing_account := type_of_clearing_account_value; filler_1 := filler_1_value; end_of_the_exposition := end_of_the_exposition_value; auction_type := auction_type_value; firm_id := firm_id_value; cmta := cmta_value |}, bytes)
                                                                  end
                                                              end
                                                          end
                                                      end
                                                  end
                                              end
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StartOfExpositionOnComplexOrderMessage.

  Module EndOfAuctionOrExpositionOnOptionMessage.

    (** End of Auction or Exposition on Option *)
    Record t := {
      exchange_id : list byte;
      instrument_description : InstrumentDescription.t;
      deletion_type : list byte;
      order_sequence_number : list byte;
      improvement_order_side : list byte;
      improvement_phase_sequential_number : list byte;
      auction_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      InstrumentDescription.bounded (instrument_description record) /\
      Datatypes.length (deletion_type record) = 1 /\
      Datatypes.length (order_sequence_number record) = 6 /\
      Datatypes.length (improvement_order_side record) = 1 /\
      Datatypes.length (improvement_phase_sequential_number record) = 6 /\
      Datatypes.length (auction_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      InstrumentDescription.encode (instrument_description record) ++
      encode_bytes 1 (deletion_type record) ++
      encode_bytes 6 (order_sequence_number record) ++
      encode_bytes 1 (improvement_order_side record) ++
      encode_bytes 6 (improvement_phase_sequential_number record) ++
      encode_bytes 1 (auction_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match InstrumentDescription.decode bytes with
          | None => None
          | Some (instrument_description_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (deletion_type_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (order_sequence_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (improvement_order_side_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (improvement_phase_sequential_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (auction_type_value, bytes) =>
                                  Some ({| exchange_id := exchange_id_value; instrument_description := instrument_description_value; deletion_type := deletion_type_value; order_sequence_number := order_sequence_number_value; improvement_order_side := improvement_order_side_value; improvement_phase_sequential_number := improvement_phase_sequential_number_value; auction_type := auction_type_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !InstrumentDescription.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite InstrumentDescription.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InstrumentDescription.eq_dec]. Defined.

  End EndOfAuctionOrExpositionOnOptionMessage.

  Module EndOfAuctionOrExpositionOnComplexInstrumentsMessage.

    (** End of Auction or Exposition on Complex Instruments *)
    Record t := {
      exchange_id : list byte;
      complex_order_instrument_symbol : list byte;
      deletion_type : list byte;
      order_sequence_number : list byte;
      order_side : list byte;
      improvement_phase_sequential_number : list byte;
      auction_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (complex_order_instrument_symbol record) = 30 /\
      Datatypes.length (deletion_type record) = 1 /\
      Datatypes.length (order_sequence_number record) = 6 /\
      Datatypes.length (order_side record) = 1 /\
      Datatypes.length (improvement_phase_sequential_number record) = 6 /\
      Datatypes.length (auction_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (complex_order_instrument_symbol record) ++
      encode_bytes 1 (deletion_type record) ++
      encode_bytes 6 (order_sequence_number record) ++
      encode_bytes 1 (order_side record) ++
      encode_bytes 6 (improvement_phase_sequential_number record) ++
      encode_bytes 1 (auction_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (complex_order_instrument_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (deletion_type_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (order_sequence_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (order_side_value, bytes) =>
                          match decode_bytes 6 bytes with
                          | None => None
                          | Some (improvement_phase_sequential_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (auction_type_value, bytes) =>
                                  Some ({| exchange_id := exchange_id_value; complex_order_instrument_symbol := complex_order_instrument_symbol_value; deletion_type := deletion_type_value; order_sequence_number := order_sequence_number_value; order_side := order_side_value; improvement_phase_sequential_number := improvement_phase_sequential_number_value; auction_type := auction_type_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EndOfAuctionOrExpositionOnComplexInstrumentsMessage.

End BoxOptionsSolaMulticastV22.
