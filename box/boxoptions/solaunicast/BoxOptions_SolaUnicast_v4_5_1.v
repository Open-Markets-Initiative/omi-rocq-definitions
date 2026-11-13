From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Box Options Market Sola Unicast

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
      - a Composite rule

    License: MIT No Attribution
  *)

Module BoxOptionsSolaUnicastV451.

  Module MessageHeader.

    (** Standard Hsvf message header *)
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

  Module GapSequenceMessage.

    (** The Gap message signals the beginning and ending sequence numbers of messages relating to classes different from those subscribed to during the connection message *)
    Record t := {
      sequence_numbers_skipped : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sequence_numbers_skipped record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (sequence_numbers_skipped record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (sequence_numbers_skipped_value, bytes) =>
          Some ({| sequence_numbers_skipped := sequence_numbers_skipped_value |}, bytes)
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

  End GapSequenceMessage.

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
      filler_1 : list byte;
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
      expiry_year : list byte;
      expiry_day : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (root_symbol record) = 6 /\
      Datatypes.length (expiry_month_code record) = 1 /\
      Datatypes.length (filler_1 record) = 1 /\
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1 /\
      Datatypes.length (expiry_year record) = 2 /\
      Datatypes.length (expiry_day record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (root_symbol record) ++
      encode_bytes 1 (expiry_month_code record) ++
      encode_bytes 1 (filler_1 record) ++
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
              match decode_bytes 1 bytes with
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

  End InstrumentDescription.

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

  Module ComplexOrderGroupStatusMessage.

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

  End ComplexOrderGroupStatusMessage.

  Module BulletinsMessage.

    (** When a Trading instrument has been halted by BOX, a Bulletin Message explaining the reason for the halt will be transmitted. *)
    Record t := {
      filler_1 : list byte;
      bulletin_type : list byte;
      bulletin_contents : list byte;
      continue_marker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (filler_1 record) = 1 /\
      Datatypes.length (bulletin_type record) = 1 /\
      Datatypes.length (bulletin_contents record) = 79 /\
      Datatypes.length (continue_marker record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (filler_1 record) ++
      encode_bytes 1 (bulletin_type record) ++
      encode_bytes 79 (bulletin_contents record) ++
      encode_bytes 1 (continue_marker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (filler_1_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bulletin_type_value, bytes) =>
              match decode_bytes 79 bytes with
              | None => None
              | Some (bulletin_contents_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (continue_marker_value, bytes) =>
                      Some ({| filler_1 := filler_1_value; bulletin_type := bulletin_type_value; bulletin_contents := bulletin_contents_value; continue_marker := continue_marker_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 82.
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

  End BulletinsMessage.

  Module EndOfSalesMessage.

    (** This message is sent when there is no more trading activity to be transmitted *)
    Record t := {
      reserved : list byte;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reserved record) = 1 /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reserved record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
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

  End EndOfSalesMessage.

  Module OptionImprovementProcessBeginningMessage.

    (** Start of Option Improvement Process *)
    Record t := {
      exchange_id : list byte;
      instrument_description : InstrumentDescription.t;
      improvement_phase_sequential_number : list byte;
      initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
      initial_order_quantity : list byte;
      initial_order_side : list byte;
      improvement_phase_expiry_time : list byte;
      improvement_process_expiry_duration : list byte;
      minimum_quantity_for_improvement_order : list byte;
      percentage_assured_to_initial_order : list byte;
      auction_type : list byte;
      filler_1 : list byte;
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
      Datatypes.length (improvement_process_expiry_duration record) = 4 /\
      Datatypes.length (minimum_quantity_for_improvement_order record) = 8 /\
      Datatypes.length (percentage_assured_to_initial_order record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      Datatypes.length (filler_1 record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      InstrumentDescription.encode (instrument_description record) ++
      encode_bytes 6 (improvement_phase_sequential_number record) ++
      encode_bytes 6 (initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record) ++
      encode_bytes 8 (initial_order_quantity record) ++
      encode_bytes 1 (initial_order_side record) ++
      encode_bytes 8 (improvement_phase_expiry_time record) ++
      encode_bytes 4 (improvement_process_expiry_duration record) ++
      encode_bytes 8 (minimum_quantity_for_improvement_order record) ++
      encode_bytes 8 (percentage_assured_to_initial_order record) ++
      encode_bytes 1 (auction_type record) ++
      encode_bytes 1 (filler_1 record).

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
                                      match decode_bytes 4 bytes with
                                      | None => None
                                      | Some (improvement_process_expiry_duration_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (minimum_quantity_for_improvement_order_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (percentage_assured_to_initial_order_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (auction_type_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (filler_1_value, bytes) =>
                                                          Some ({| exchange_id := exchange_id_value; instrument_description := instrument_description_value; improvement_phase_sequential_number := improvement_phase_sequential_number_value; initial_order_price := initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value; initial_order_quantity := initial_order_quantity_value; initial_order_side := initial_order_side_value; improvement_phase_expiry_time := improvement_phase_expiry_time_value; improvement_process_expiry_duration := improvement_process_expiry_duration_value; minimum_quantity_for_improvement_order := minimum_quantity_for_improvement_order_value; percentage_assured_to_initial_order := percentage_assured_to_initial_order_value; auction_type := auction_type_value; filler_1 := filler_1_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length, !InstrumentDescription.encode_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply InstrumentDescription.eq_dec]. Defined.

  End OptionImprovementProcessBeginningMessage.

  Module ComplexOrderImprovementProcessBeginningMessageMessage.

    (** Complex Order Improvement Process Beginning Message *)
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
      improvement_process_expiry_duration : list byte;
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
      Datatypes.length (improvement_process_expiry_duration record) = 4 /\
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
      encode_bytes 4 (improvement_process_expiry_duration record) ++
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
                                          match decode_bytes 4 bytes with
                                          | None => None
                                          | Some (improvement_process_expiry_duration_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (minimum_quantity_for_improvement_order_value, bytes) =>
                                                  match decode_bytes 8 bytes with
                                                  | None => None
                                                  | Some (percentage_assured_to_initial_order_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (auction_type_value, bytes) =>
                                                          Some ({| exchange_id := exchange_id_value; complex_order_instrument_symbol := complex_order_instrument_symbol_value; improvement_phase_sequential_number := improvement_phase_sequential_number_value; initial_order_price_sign := initial_order_price_sign_value; initial_order_price := initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value; initial_order_quantity := initial_order_quantity_value; initial_order_side := initial_order_side_value; improvement_phase_expiry_time := improvement_phase_expiry_time_value; improvement_process_expiry_duration := improvement_process_expiry_duration_value; minimum_quantity_for_improvement_order := minimum_quantity_for_improvement_order_value; percentage_assured_to_initial_order := percentage_assured_to_initial_order_value; auction_type := auction_type_value |}, bytes)
                                                      end
                                                  end
                                              end
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
      rewrite !length_app, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexOrderImprovementProcessBeginningMessageMessage.

  Module InitialAndImprovementOrderMessage.

    (** Initial and Improvement Order (Options) / Exposed Order *)
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

  End InitialAndImprovementOrderMessage.

  Module ComplexOrderInitialAndImprovementOrderMessage.

    (** Initial and Improvement Order (Complex Order) / Exposed Order (Complex Order) *)
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

  End ComplexOrderInitialAndImprovementOrderMessage.

End BoxOptionsSolaUnicastV451.
