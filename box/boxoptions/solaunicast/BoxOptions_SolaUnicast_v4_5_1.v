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
      - the dispatch that chooses a message by its type
      - a Composite rule
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

  Module StrikePriceNegativeWholePair.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair.

  Module StrikePriceNegativeTenPair.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair.

  Module StrikePriceNegativeHundredPair.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair.

  Module StrikePriceNegativeThousandPair.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair.

  Module StrikePriceNegativeTenThousandPair.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair.

  Module StrikePriceNegativeHundredThousandPair.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair.

  Module StrikePriceNegativeMillionPair.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair.

  Module StrikePriceNumericPair.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair.

  Module StrikePriceUnknownFractionPair.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair.

  Module TradePriceNegativeWholePair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeWholePair.

  Module TradePriceNegativeTenPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenPair.

  Module TradePriceNegativeHundredPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredPair.

  Module TradePriceNegativeThousandPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeThousandPair.

  Module TradePriceNegativeTenThousandPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenThousandPair.

  Module TradePriceNegativeHundredThousandPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredThousandPair.

  Module TradePriceNegativeMillionPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeMillionPair.

  Module TradePriceNumericPair.

    Record t := {
      trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| trade_price := trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNumericPair.

  Module TradePriceUnknownFractionPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceUnknownFractionPair.

  Module NetChangeNegativeWholePair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeWholePair.

  Module NetChangeNegativeTenPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenPair.

  Module NetChangeNegativeHundredPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredPair.

  Module NetChangeNegativeThousandPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeThousandPair.

  Module NetChangeNegativeTenThousandPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenThousandPair.

  Module NetChangeNegativeHundredThousandPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredThousandPair.

  Module NetChangeNegativeMillionPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeMillionPair.

  Module NetChangeNumericPair.

    Record t := {
      net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| net_change := net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNumericPair.

  Module NetChangeUnknownFractionPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeUnknownFractionPair.

  Module TradePriceNegativeWholePair2.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeWholePair2.

  Module TradePriceNegativeTenPair2.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenPair2.

  Module TradePriceNegativeHundredPair2.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredPair2.

  Module TradePriceNegativeThousandPair2.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeThousandPair2.

  Module TradePriceNegativeTenThousandPair2.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenThousandPair2.

  Module TradePriceNegativeHundredThousandPair2.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredThousandPair2.

  Module TradePriceNegativeMillionPair2.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeMillionPair2.

  Module TradePriceNumericPair2.

    Record t := {
      trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| trade_price := trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNumericPair2.

  Module TradePriceUnknownFractionPair2.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceUnknownFractionPair2.

  Module NetChangeNegativeWholePair2.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeWholePair2.

  Module NetChangeNegativeTenPair2.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenPair2.

  Module NetChangeNegativeHundredPair2.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredPair2.

  Module NetChangeNegativeThousandPair2.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeThousandPair2.

  Module NetChangeNegativeTenThousandPair2.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenThousandPair2.

  Module NetChangeNegativeHundredThousandPair2.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredThousandPair2.

  Module NetChangeNegativeMillionPair2.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeMillionPair2.

  Module NetChangeNumericPair2.

    Record t := {
      net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| net_change := net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNumericPair2.

  Module NetChangeUnknownFractionPair2.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeUnknownFractionPair2.

  Module StrikePriceNegativeWholePair2.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair2.

  Module StrikePriceNegativeTenPair2.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair2.

  Module StrikePriceNegativeHundredPair2.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair2.

  Module StrikePriceNegativeThousandPair2.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair2.

  Module StrikePriceNegativeTenThousandPair2.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair2.

  Module StrikePriceNegativeHundredThousandPair2.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair2.

  Module StrikePriceNegativeMillionPair2.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair2.

  Module StrikePriceNumericPair2.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair2.

  Module StrikePriceUnknownFractionPair2.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair2.

  Module StrikePriceNegativeWholePair3.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair3.

  Module StrikePriceNegativeTenPair3.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair3.

  Module StrikePriceNegativeHundredPair3.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair3.

  Module StrikePriceNegativeThousandPair3.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair3.

  Module StrikePriceNegativeTenThousandPair3.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair3.

  Module StrikePriceNegativeHundredThousandPair3.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair3.

  Module StrikePriceNegativeMillionPair3.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair3.

  Module StrikePriceNumericPair3.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair3.

  Module StrikePriceUnknownFractionPair3.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair3.

  Module BidPriceQuoteNegativeWholePair.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeWholePair.

  Module BidPriceQuoteNegativeTenPair.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeTenPair.

  Module BidPriceQuoteNegativeHundredPair.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeHundredPair.

  Module BidPriceQuoteNegativeThousandPair.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeThousandPair.

  Module BidPriceQuoteNegativeTenThousandPair.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeTenThousandPair.

  Module BidPriceQuoteNegativeHundredThousandPair.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeHundredThousandPair.

  Module BidPriceQuoteNegativeMillionPair.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeMillionPair.

  Module BidPriceQuoteOpeningPair.

    Record t := {
      bid_price_quote_opening : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_opening record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_quote_opening record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_opening := bid_price_quote_opening_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteOpeningPair.

  Module BidPriceQuoteNumericPair.

    Record t := {
      bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_numeric := bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericPair.

  Module BidPriceQuoteUnknownFractionPair.

    Record t := {
      raw_bid_price_quote_text : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_text record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_text record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_text_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_text := raw_bid_price_quote_text_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteUnknownFractionPair.

  Module AskPriceQuoteNegativeWholePair.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeWholePair.

  Module AskPriceQuoteNegativeTenPair.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeTenPair.

  Module AskPriceQuoteNegativeHundredPair.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeHundredPair.

  Module AskPriceQuoteNegativeThousandPair.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeThousandPair.

  Module AskPriceQuoteNegativeTenThousandPair.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeTenThousandPair.

  Module AskPriceQuoteNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeHundredThousandPair.

  Module AskPriceQuoteNegativeMillionPair.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeMillionPair.

  Module AskPriceQuoteOpeningPair.

    Record t := {
      ask_price_quote_opening : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_opening record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_quote_opening record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_opening := ask_price_quote_opening_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteOpeningPair.

  Module AskPriceQuoteNumericPair.

    Record t := {
      ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_numeric := ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericPair.

  Module AskPriceQuoteUnknownFractionPair.

    Record t := {
      raw_ask_price_quote_text : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_text record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_text record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_text_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_text := raw_ask_price_quote_text_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteUnknownFractionPair.

  Module BidPriceQuoteNegativeWholePair2.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeWholePair2.

  Module BidPriceQuoteNegativeTenPair2.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeTenPair2.

  Module BidPriceQuoteNegativeHundredPair2.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeHundredPair2.

  Module BidPriceQuoteNegativeThousandPair2.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeThousandPair2.

  Module BidPriceQuoteNegativeTenThousandPair2.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeTenThousandPair2.

  Module BidPriceQuoteNegativeHundredThousandPair2.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeHundredThousandPair2.

  Module BidPriceQuoteNegativeMillionPair2.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeMillionPair2.

  Module BidPriceQuoteOpeningPair2.

    Record t := {
      bid_price_quote_opening : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_opening record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_quote_opening record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_opening := bid_price_quote_opening_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteOpeningPair2.

  Module BidPriceQuoteNumericPair2.

    Record t := {
      bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_numeric := bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericPair2.

  Module BidPriceQuoteUnknownFractionPair2.

    Record t := {
      raw_bid_price_quote_text : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_text record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_text record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_text_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_text := raw_bid_price_quote_text_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteUnknownFractionPair2.

  Module AskPriceQuoteNegativeWholePair2.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeWholePair2.

  Module AskPriceQuoteNegativeTenPair2.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeTenPair2.

  Module AskPriceQuoteNegativeHundredPair2.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeHundredPair2.

  Module AskPriceQuoteNegativeThousandPair2.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeThousandPair2.

  Module AskPriceQuoteNegativeTenThousandPair2.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeTenThousandPair2.

  Module AskPriceQuoteNegativeHundredThousandPair2.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeHundredThousandPair2.

  Module AskPriceQuoteNegativeMillionPair2.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeMillionPair2.

  Module AskPriceQuoteOpeningPair2.

    Record t := {
      ask_price_quote_opening : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_opening record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_quote_opening record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_opening := ask_price_quote_opening_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteOpeningPair2.

  Module AskPriceQuoteNumericPair2.

    Record t := {
      ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_numeric := ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericPair2.

  Module AskPriceQuoteUnknownFractionPair2.

    Record t := {
      raw_ask_price_quote_text : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_text record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_text record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_text_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_text := raw_ask_price_quote_text_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteUnknownFractionPair2.

  Module StrikePriceNegativeWholePair4.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair4.

  Module StrikePriceNegativeTenPair4.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair4.

  Module StrikePriceNegativeHundredPair4.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair4.

  Module StrikePriceNegativeThousandPair4.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair4.

  Module StrikePriceNegativeTenThousandPair4.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair4.

  Module StrikePriceNegativeHundredThousandPair4.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair4.

  Module StrikePriceNegativeMillionPair4.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair4.

  Module StrikePriceNumericPair4.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair4.

  Module StrikePriceUnknownFractionPair4.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair4.

  Module BidPriceQuoteNegativeWholePair3.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeWholePair3.

  Module BidPriceQuoteNegativeTenPair3.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeTenPair3.

  Module BidPriceQuoteNegativeHundredPair3.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeHundredPair3.

  Module BidPriceQuoteNegativeThousandPair3.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeThousandPair3.

  Module BidPriceQuoteNegativeTenThousandPair3.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeTenThousandPair3.

  Module BidPriceQuoteNegativeHundredThousandPair3.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeHundredThousandPair3.

  Module BidPriceQuoteNegativeMillionPair3.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeMillionPair3.

  Module BidPriceQuoteOpeningPair3.

    Record t := {
      bid_price_quote_opening : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_opening record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_quote_opening record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_opening := bid_price_quote_opening_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteOpeningPair3.

  Module BidPriceQuoteNumericPair3.

    Record t := {
      bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_numeric := bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericPair3.

  Module BidPriceQuoteUnknownFractionPair3.

    Record t := {
      raw_bid_price_quote_text : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_text record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_text record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_text_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_text := raw_bid_price_quote_text_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteUnknownFractionPair3.

  Module AskPriceQuoteNegativeWholePair3.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeWholePair3.

  Module AskPriceQuoteNegativeTenPair3.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeTenPair3.

  Module AskPriceQuoteNegativeHundredPair3.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeHundredPair3.

  Module AskPriceQuoteNegativeThousandPair3.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeThousandPair3.

  Module AskPriceQuoteNegativeTenThousandPair3.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeTenThousandPair3.

  Module AskPriceQuoteNegativeHundredThousandPair3.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeHundredThousandPair3.

  Module AskPriceQuoteNegativeMillionPair3.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeMillionPair3.

  Module AskPriceQuoteOpeningPair3.

    Record t := {
      ask_price_quote_opening : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_opening record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_quote_opening record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_opening := ask_price_quote_opening_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteOpeningPair3.

  Module AskPriceQuoteNumericPair3.

    Record t := {
      ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_numeric := ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericPair3.

  Module AskPriceQuoteUnknownFractionPair3.

    Record t := {
      raw_ask_price_quote_text : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_text record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_text record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_text_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_text := raw_ask_price_quote_text_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteUnknownFractionPair3.

  Module BidPriceQuoteNegativeWholePair4.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeWholePair4.

  Module BidPriceQuoteNegativeTenPair4.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeTenPair4.

  Module BidPriceQuoteNegativeHundredPair4.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeHundredPair4.

  Module BidPriceQuoteNegativeThousandPair4.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeThousandPair4.

  Module BidPriceQuoteNegativeTenThousandPair4.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeTenThousandPair4.

  Module BidPriceQuoteNegativeHundredThousandPair4.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeHundredThousandPair4.

  Module BidPriceQuoteNegativeMillionPair4.

    Record t := {
      raw_bid_price_quote : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote := raw_bid_price_quote_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNegativeMillionPair4.

  Module BidPriceQuoteOpeningPair4.

    Record t := {
      bid_price_quote_opening : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_opening record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_quote_opening record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_opening := bid_price_quote_opening_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteOpeningPair4.

  Module BidPriceQuoteNumericPair4.

    Record t := {
      bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_numeric := bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericPair4.

  Module BidPriceQuoteUnknownFractionPair4.

    Record t := {
      raw_bid_price_quote_text : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_text record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_text record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_text_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_text := raw_bid_price_quote_text_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteUnknownFractionPair4.

  Module AskPriceQuoteNegativeWholePair4.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeWholePair4.

  Module AskPriceQuoteNegativeTenPair4.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeTenPair4.

  Module AskPriceQuoteNegativeHundredPair4.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeHundredPair4.

  Module AskPriceQuoteNegativeThousandPair4.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeThousandPair4.

  Module AskPriceQuoteNegativeTenThousandPair4.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeTenThousandPair4.

  Module AskPriceQuoteNegativeHundredThousandPair4.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeHundredThousandPair4.

  Module AskPriceQuoteNegativeMillionPair4.

    Record t := {
      raw_ask_price_quote : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote := raw_ask_price_quote_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNegativeMillionPair4.

  Module AskPriceQuoteOpeningPair4.

    Record t := {
      ask_price_quote_opening : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_opening record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_quote_opening record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_opening := ask_price_quote_opening_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteOpeningPair4.

  Module AskPriceQuoteNumericPair4.

    Record t := {
      ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_numeric := ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericPair4.

  Module AskPriceQuoteUnknownFractionPair4.

    Record t := {
      raw_ask_price_quote_text : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_text record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_text record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_text_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_text := raw_ask_price_quote_text_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteUnknownFractionPair4.

  Module StrikePriceNegativeWholePair5.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair5.

  Module StrikePriceNegativeTenPair5.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair5.

  Module StrikePriceNegativeHundredPair5.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair5.

  Module StrikePriceNegativeThousandPair5.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair5.

  Module StrikePriceNegativeTenThousandPair5.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair5.

  Module StrikePriceNegativeHundredThousandPair5.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair5.

  Module StrikePriceNegativeMillionPair5.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair5.

  Module StrikePriceNumericPair5.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair5.

  Module StrikePriceUnknownFractionPair5.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair5.

  Module TradePriceNegativeWholePair3.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeWholePair3.

  Module TradePriceNegativeTenPair3.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenPair3.

  Module TradePriceNegativeHundredPair3.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredPair3.

  Module TradePriceNegativeThousandPair3.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeThousandPair3.

  Module TradePriceNegativeTenThousandPair3.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenThousandPair3.

  Module TradePriceNegativeHundredThousandPair3.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredThousandPair3.

  Module TradePriceNegativeMillionPair3.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeMillionPair3.

  Module TradePriceNumericPair3.

    Record t := {
      trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| trade_price := trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNumericPair3.

  Module TradePriceUnknownFractionPair3.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceUnknownFractionPair3.

  Module TradePriceNegativeWholePair4.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeWholePair4.

  Module TradePriceNegativeTenPair4.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenPair4.

  Module TradePriceNegativeHundredPair4.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredPair4.

  Module TradePriceNegativeThousandPair4.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeThousandPair4.

  Module TradePriceNegativeTenThousandPair4.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenThousandPair4.

  Module TradePriceNegativeHundredThousandPair4.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredThousandPair4.

  Module TradePriceNegativeMillionPair4.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeMillionPair4.

  Module TradePriceNumericPair4.

    Record t := {
      trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| trade_price := trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNumericPair4.

  Module TradePriceUnknownFractionPair4.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 6 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceUnknownFractionPair4.

  Module StrikePriceNegativeWholePair6.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair6.

  Module StrikePriceNegativeTenPair6.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair6.

  Module StrikePriceNegativeHundredPair6.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair6.

  Module StrikePriceNegativeThousandPair6.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair6.

  Module StrikePriceNegativeTenThousandPair6.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair6.

  Module StrikePriceNegativeHundredThousandPair6.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair6.

  Module StrikePriceNegativeMillionPair6.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair6.

  Module StrikePriceNumericPair6.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair6.

  Module StrikePriceUnknownFractionPair6.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair6.

  Module TickIncrementTickTablePair.

    Record t := {
      raw_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment := raw_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementTickTablePair.

  Module TickIncrementNegativeWholePair.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeWholePair.

  Module TickIncrementNegativeTenPair.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeTenPair.

  Module TickIncrementNegativeHundredPair.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeHundredPair.

  Module TickIncrementNegativeThousandPair.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeThousandPair.

  Module TickIncrementNegativeTenThousandPair.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeTenThousandPair.

  Module TickIncrementNegativeHundredThousandPair.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeHundredThousandPair.

  Module TickIncrementNegativeMillionPair.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeMillionPair.

  Module TickIncrementNumericPair.

    Record t := {
      tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| tick_increment := tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericPair.

  Module TickIncrementUnknownFractionPair.

    Record t := {
      raw_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment := raw_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementUnknownFractionPair.

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

  Module TickIncrementTickTablePair2.

    Record t := {
      raw_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment := raw_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementTickTablePair2.

  Module TickIncrementNegativeWholePair2.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeWholePair2.

  Module TickIncrementNegativeTenPair2.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeTenPair2.

  Module TickIncrementNegativeHundredPair2.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeHundredPair2.

  Module TickIncrementNegativeThousandPair2.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeThousandPair2.

  Module TickIncrementNegativeTenThousandPair2.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeTenThousandPair2.

  Module TickIncrementNegativeHundredThousandPair2.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeHundredThousandPair2.

  Module TickIncrementNegativeMillionPair2.

    Record t := {
      numeric_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (numeric_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (numeric_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (numeric_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| numeric_tick_increment := numeric_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNegativeMillionPair2.

  Module TickIncrementNumericPair2.

    Record t := {
      tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| tick_increment := tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericPair2.

  Module TickIncrementUnknownFractionPair2.

    Record t := {
      raw_tick_increment : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment := raw_tick_increment_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementUnknownFractionPair2.

  Module StrikePriceNegativeWholePair7.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair7.

  Module StrikePriceNegativeTenPair7.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair7.

  Module StrikePriceNegativeHundredPair7.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair7.

  Module StrikePriceNegativeThousandPair7.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair7.

  Module StrikePriceNegativeTenThousandPair7.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair7.

  Module StrikePriceNegativeHundredThousandPair7.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair7.

  Module StrikePriceNegativeMillionPair7.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair7.

  Module StrikePriceNumericPair7.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair7.

  Module StrikePriceUnknownFractionPair7.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair7.

  Module BidPriceNegativeWholePair.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeWholePair.

  Module BidPriceNegativeTenPair.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeTenPair.

  Module BidPriceNegativeHundredPair.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeHundredPair.

  Module BidPriceNegativeThousandPair.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeThousandPair.

  Module BidPriceNegativeTenThousandPair.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeTenThousandPair.

  Module BidPriceNegativeHundredThousandPair.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeHundredThousandPair.

  Module BidPriceNegativeMillionPair.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeMillionPair.

  Module BidPriceNumericPair.

    Record t := {
      bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price := bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNumericPair.

  Module BidPriceUnknownFractionPair.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceUnknownFractionPair.

  Module AskPriceNegativeWholePair.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeWholePair.

  Module AskPriceNegativeTenPair.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeTenPair.

  Module AskPriceNegativeHundredPair.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeHundredPair.

  Module AskPriceNegativeThousandPair.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeThousandPair.

  Module AskPriceNegativeTenThousandPair.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeTenThousandPair.

  Module AskPriceNegativeHundredThousandPair.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeHundredThousandPair.

  Module AskPriceNegativeMillionPair.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeMillionPair.

  Module AskPriceNumericPair.

    Record t := {
      ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price := ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNumericPair.

  Module AskPriceUnknownFractionPair.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceUnknownFractionPair.

  Module LastPriceNegativeWholePair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeWholePair.

  Module LastPriceNegativeTenPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeTenPair.

  Module LastPriceNegativeHundredPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeHundredPair.

  Module LastPriceNegativeThousandPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeThousandPair.

  Module LastPriceNegativeTenThousandPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeTenThousandPair.

  Module LastPriceNegativeHundredThousandPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeHundredThousandPair.

  Module LastPriceNegativeMillionPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeMillionPair.

  Module LastPriceNumericPair.

    Record t := {
      last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| last_price := last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNumericPair.

  Module LastPriceUnknownFractionPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceUnknownFractionPair.

  Module NetChangeNegativeWholePair3.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeWholePair3.

  Module NetChangeNegativeTenPair3.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenPair3.

  Module NetChangeNegativeHundredPair3.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredPair3.

  Module NetChangeNegativeThousandPair3.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeThousandPair3.

  Module NetChangeNegativeTenThousandPair3.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenThousandPair3.

  Module NetChangeNegativeHundredThousandPair3.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredThousandPair3.

  Module NetChangeNegativeMillionPair3.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeMillionPair3.

  Module NetChangeNumericPair3.

    Record t := {
      net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| net_change := net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNumericPair3.

  Module NetChangeUnknownFractionPair3.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeUnknownFractionPair3.

  Module OpenPriceNegativeWholePair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeWholePair.

  Module OpenPriceNegativeTenPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeTenPair.

  Module OpenPriceNegativeHundredPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeHundredPair.

  Module OpenPriceNegativeThousandPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeThousandPair.

  Module OpenPriceNegativeTenThousandPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeTenThousandPair.

  Module OpenPriceNegativeHundredThousandPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeHundredThousandPair.

  Module OpenPriceNegativeMillionPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeMillionPair.

  Module OpenPriceNumericPair.

    Record t := {
      open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| open_price := open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNumericPair.

  Module OpenPriceUnknownFractionPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceUnknownFractionPair.

  Module HighPriceNegativeWholePair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeWholePair.

  Module HighPriceNegativeTenPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeTenPair.

  Module HighPriceNegativeHundredPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeHundredPair.

  Module HighPriceNegativeThousandPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeThousandPair.

  Module HighPriceNegativeTenThousandPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeTenThousandPair.

  Module HighPriceNegativeHundredThousandPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeHundredThousandPair.

  Module HighPriceNegativeMillionPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeMillionPair.

  Module HighPriceNumericPair.

    Record t := {
      high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| high_price := high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNumericPair.

  Module HighPriceUnknownFractionPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceUnknownFractionPair.

  Module LowPriceNegativeWholePair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeWholePair.

  Module LowPriceNegativeTenPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeTenPair.

  Module LowPriceNegativeHundredPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeHundredPair.

  Module LowPriceNegativeThousandPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeThousandPair.

  Module LowPriceNegativeTenThousandPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeTenThousandPair.

  Module LowPriceNegativeHundredThousandPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeHundredThousandPair.

  Module LowPriceNegativeMillionPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeMillionPair.

  Module LowPriceNumericPair.

    Record t := {
      low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| low_price := low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNumericPair.

  Module LowPriceUnknownFractionPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceUnknownFractionPair.

  Module OptionMarker2.

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

  End OptionMarker2.

  Module ReferencePriceNegativeWholePair.

    Record t := {
      raw_reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| raw_reference_price := raw_reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceNegativeWholePair.

  Module ReferencePriceNegativeTenPair.

    Record t := {
      raw_reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| raw_reference_price := raw_reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceNegativeTenPair.

  Module ReferencePriceNegativeHundredPair.

    Record t := {
      raw_reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| raw_reference_price := raw_reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceNegativeHundredPair.

  Module ReferencePriceNegativeThousandPair.

    Record t := {
      raw_reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| raw_reference_price := raw_reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceNegativeThousandPair.

  Module ReferencePriceNegativeTenThousandPair.

    Record t := {
      raw_reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| raw_reference_price := raw_reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceNegativeTenThousandPair.

  Module ReferencePriceNegativeHundredThousandPair.

    Record t := {
      raw_reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| raw_reference_price := raw_reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceNegativeHundredThousandPair.

  Module ReferencePriceNegativeMillionPair.

    Record t := {
      raw_reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| raw_reference_price := raw_reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceNegativeMillionPair.

  Module ReferencePriceNumericPair.

    Record t := {
      reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| reference_price := reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceNumericPair.

  Module ReferencePriceUnknownFractionPair.

    Record t := {
      raw_reference_price : list byte;
      reference_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_reference_price record) = 6 /\
      Datatypes.length (reference_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_reference_price record) ++
      encode_bytes 1 (reference_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_reference_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_fraction_indicator_value, bytes) =>
              Some ({| raw_reference_price := raw_reference_price_value; reference_price_fraction_indicator := reference_price_fraction_indicator_value |}, bytes)
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

  End ReferencePriceUnknownFractionPair.

  Module BidPriceNegativeWholePair2.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeWholePair2.

  Module BidPriceNegativeTenPair2.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeTenPair2.

  Module BidPriceNegativeHundredPair2.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeHundredPair2.

  Module BidPriceNegativeThousandPair2.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeThousandPair2.

  Module BidPriceNegativeTenThousandPair2.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeTenThousandPair2.

  Module BidPriceNegativeHundredThousandPair2.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeHundredThousandPair2.

  Module BidPriceNegativeMillionPair2.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNegativeMillionPair2.

  Module BidPriceNumericPair2.

    Record t := {
      bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price := bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceNumericPair2.

  Module BidPriceUnknownFractionPair2.

    Record t := {
      raw_bid_price : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price := raw_bid_price_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceUnknownFractionPair2.

  Module AskPriceNegativeWholePair2.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeWholePair2.

  Module AskPriceNegativeTenPair2.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeTenPair2.

  Module AskPriceNegativeHundredPair2.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeHundredPair2.

  Module AskPriceNegativeThousandPair2.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeThousandPair2.

  Module AskPriceNegativeTenThousandPair2.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeTenThousandPair2.

  Module AskPriceNegativeHundredThousandPair2.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeHundredThousandPair2.

  Module AskPriceNegativeMillionPair2.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNegativeMillionPair2.

  Module AskPriceNumericPair2.

    Record t := {
      ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price := ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceNumericPair2.

  Module AskPriceUnknownFractionPair2.

    Record t := {
      raw_ask_price : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price := raw_ask_price_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceUnknownFractionPair2.

  Module LastPriceNegativeWholePair2.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeWholePair2.

  Module LastPriceNegativeTenPair2.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeTenPair2.

  Module LastPriceNegativeHundredPair2.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeHundredPair2.

  Module LastPriceNegativeThousandPair2.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeThousandPair2.

  Module LastPriceNegativeTenThousandPair2.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeTenThousandPair2.

  Module LastPriceNegativeHundredThousandPair2.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeHundredThousandPair2.

  Module LastPriceNegativeMillionPair2.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeMillionPair2.

  Module LastPriceNumericPair2.

    Record t := {
      last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| last_price := last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNumericPair2.

  Module LastPriceUnknownFractionPair2.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceUnknownFractionPair2.

  Module OpenPriceNegativeWholePair2.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeWholePair2.

  Module OpenPriceNegativeTenPair2.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeTenPair2.

  Module OpenPriceNegativeHundredPair2.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeHundredPair2.

  Module OpenPriceNegativeThousandPair2.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeThousandPair2.

  Module OpenPriceNegativeTenThousandPair2.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeTenThousandPair2.

  Module OpenPriceNegativeHundredThousandPair2.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeHundredThousandPair2.

  Module OpenPriceNegativeMillionPair2.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeMillionPair2.

  Module OpenPriceNumericPair2.

    Record t := {
      open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| open_price := open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNumericPair2.

  Module OpenPriceUnknownFractionPair2.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 6 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceUnknownFractionPair2.

  Module HighPriceNegativeWholePair2.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeWholePair2.

  Module HighPriceNegativeTenPair2.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeTenPair2.

  Module HighPriceNegativeHundredPair2.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeHundredPair2.

  Module HighPriceNegativeThousandPair2.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeThousandPair2.

  Module HighPriceNegativeTenThousandPair2.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeTenThousandPair2.

  Module HighPriceNegativeHundredThousandPair2.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeHundredThousandPair2.

  Module HighPriceNegativeMillionPair2.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeMillionPair2.

  Module HighPriceNumericPair2.

    Record t := {
      high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| high_price := high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNumericPair2.

  Module HighPriceUnknownFractionPair2.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 6 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceUnknownFractionPair2.

  Module LowPriceNegativeWholePair2.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeWholePair2.

  Module LowPriceNegativeTenPair2.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeTenPair2.

  Module LowPriceNegativeHundredPair2.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeHundredPair2.

  Module LowPriceNegativeThousandPair2.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeThousandPair2.

  Module LowPriceNegativeTenThousandPair2.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeTenThousandPair2.

  Module LowPriceNegativeHundredThousandPair2.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeHundredThousandPair2.

  Module LowPriceNegativeMillionPair2.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeMillionPair2.

  Module LowPriceNumericPair2.

    Record t := {
      low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| low_price := low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNumericPair2.

  Module LowPriceUnknownFractionPair2.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 6 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceUnknownFractionPair2.

  Module NetChangeNegativeWholePair4.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeWholePair4.

  Module NetChangeNegativeTenPair4.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenPair4.

  Module NetChangeNegativeHundredPair4.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredPair4.

  Module NetChangeNegativeThousandPair4.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeThousandPair4.

  Module NetChangeNegativeTenThousandPair4.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenThousandPair4.

  Module NetChangeNegativeHundredThousandPair4.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredThousandPair4.

  Module NetChangeNegativeMillionPair4.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeMillionPair4.

  Module NetChangeNumericPair4.

    Record t := {
      net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| net_change := net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNumericPair4.

  Module NetChangeUnknownFractionPair4.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeUnknownFractionPair4.

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
      filler_1 : N;
      bulletin_type : list byte;
      bulletin_contents : list byte;
      continue_marker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (bulletin_type record) = 1 /\
      Datatypes.length (bulletin_contents record) = 79 /\
      Datatypes.length (continue_marker record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (filler_1 record) ++
      encode_bytes 1 (bulletin_type record) ++
      encode_bytes 79 (bulletin_contents record) ++
      encode_bytes 1 (continue_marker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
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

  End BulletinsMessage.

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

  Module StrikePriceNegativeWholePair8.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair8.

  Module StrikePriceNegativeTenPair8.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair8.

  Module StrikePriceNegativeHundredPair8.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair8.

  Module StrikePriceNegativeThousandPair8.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair8.

  Module StrikePriceNegativeTenThousandPair8.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair8.

  Module StrikePriceNegativeHundredThousandPair8.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair8.

  Module StrikePriceNegativeMillionPair8.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair8.

  Module StrikePriceNumericPair8.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair8.

  Module StrikePriceUnknownFractionPair8.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair8.

  Module InitialOrderPriceNegativeWholePair.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeWholePair.

  Module InitialOrderPriceNegativeTenPair.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeTenPair.

  Module InitialOrderPriceNegativeHundredPair.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeHundredPair.

  Module InitialOrderPriceNegativeThousandPair.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeThousandPair.

  Module InitialOrderPriceNegativeTenThousandPair.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeTenThousandPair.

  Module InitialOrderPriceNegativeHundredThousandPair.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeHundredThousandPair.

  Module InitialOrderPriceNegativeMillionPair.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeMillionPair.

  Module InitialOrderPriceNumericPair.

    Record t := {
      initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| initial_order_price := initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNumericPair.

  Module InitialOrderPriceUnknownFractionPair.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceUnknownFractionPair.

  Module InitialOrderPriceNegativeWholePair2.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeWholePair2.

  Module InitialOrderPriceNegativeTenPair2.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeTenPair2.

  Module InitialOrderPriceNegativeHundredPair2.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeHundredPair2.

  Module InitialOrderPriceNegativeThousandPair2.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeThousandPair2.

  Module InitialOrderPriceNegativeTenThousandPair2.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeTenThousandPair2.

  Module InitialOrderPriceNegativeHundredThousandPair2.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeHundredThousandPair2.

  Module InitialOrderPriceNegativeMillionPair2.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNegativeMillionPair2.

  Module InitialOrderPriceNumericPair2.

    Record t := {
      initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| initial_order_price := initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceNumericPair2.

  Module InitialOrderPriceUnknownFractionPair2.

    Record t := {
      raw_initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_initial_order_price record) = 6 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| raw_initial_order_price := raw_initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
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

  End InitialOrderPriceUnknownFractionPair2.

  Module StrikePriceNegativeWholePair9.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair9.

  Module StrikePriceNegativeTenPair9.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair9.

  Module StrikePriceNegativeHundredPair9.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair9.

  Module StrikePriceNegativeThousandPair9.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair9.

  Module StrikePriceNegativeTenThousandPair9.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair9.

  Module StrikePriceNegativeHundredThousandPair9.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair9.

  Module StrikePriceNegativeMillionPair9.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair9.

  Module StrikePriceNumericPair9.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair9.

  Module StrikePriceUnknownFractionPair9.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair9.

  Module LimitEnteredForAnOrderNegativeWholePair.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeWholePair.

  Module LimitEnteredForAnOrderNegativeTenPair.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeTenPair.

  Module LimitEnteredForAnOrderNegativeHundredPair.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeHundredPair.

  Module LimitEnteredForAnOrderNegativeThousandPair.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeThousandPair.

  Module LimitEnteredForAnOrderNegativeTenThousandPair.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeTenThousandPair.

  Module LimitEnteredForAnOrderNegativeHundredThousandPair.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeHundredThousandPair.

  Module LimitEnteredForAnOrderNegativeMillionPair.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeMillionPair.

  Module LimitEnteredForAnOrderNumericPair.

    Record t := {
      limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| limit_entered_for_an_order := limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNumericPair.

  Module LimitEnteredForAnOrderUnknownFractionPair.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderUnknownFractionPair.

  Module LimitEnteredForAnOrderNegativeWholePair2.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeWholePair2.

  Module LimitEnteredForAnOrderNegativeTenPair2.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeTenPair2.

  Module LimitEnteredForAnOrderNegativeHundredPair2.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeHundredPair2.

  Module LimitEnteredForAnOrderNegativeThousandPair2.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeThousandPair2.

  Module LimitEnteredForAnOrderNegativeTenThousandPair2.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeTenThousandPair2.

  Module LimitEnteredForAnOrderNegativeHundredThousandPair2.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeHundredThousandPair2.

  Module LimitEnteredForAnOrderNegativeMillionPair2.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNegativeMillionPair2.

  Module LimitEnteredForAnOrderNumericPair2.

    Record t := {
      limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| limit_entered_for_an_order := limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderNumericPair2.

  Module LimitEnteredForAnOrderUnknownFractionPair2.

    Record t := {
      raw_limit_entered_for_an_order : list byte;
      limit_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_limit_entered_for_an_order record) = 6 /\
      Datatypes.length (limit_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_limit_entered_for_an_order record) ++
      encode_bytes 1 (limit_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_limit_entered_for_an_order_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (limit_fraction_indicator_value, bytes) =>
              Some ({| raw_limit_entered_for_an_order := raw_limit_entered_for_an_order_value; limit_fraction_indicator := limit_fraction_indicator_value |}, bytes)
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

  End LimitEnteredForAnOrderUnknownFractionPair2.

  Module StrikePriceNegativeWholePair10.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeWholePair10.

  Module StrikePriceNegativeTenPair10.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenPair10.

  Module StrikePriceNegativeHundredPair10.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredPair10.

  Module StrikePriceNegativeThousandPair10.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeThousandPair10.

  Module StrikePriceNegativeTenThousandPair10.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeTenThousandPair10.

  Module StrikePriceNegativeHundredThousandPair10.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeHundredThousandPair10.

  Module StrikePriceNegativeMillionPair10.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNegativeMillionPair10.

  Module StrikePriceNumericPair10.

    Record t := {
      strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price := strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceNumericPair10.

  Module StrikePriceUnknownFractionPair10.

    Record t := {
      raw_strike_price : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price := raw_strike_price_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrikePriceUnknownFractionPair10.

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
