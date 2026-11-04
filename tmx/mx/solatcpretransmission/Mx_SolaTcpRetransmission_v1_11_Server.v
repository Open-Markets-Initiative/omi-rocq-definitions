From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * TMX Group Sola Tcp Retransmission

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
      - the dispatch that chooses a message by its type
      - a run counted by a field

    License: MIT No Attribution
  *)

Module MxSolaTcpRetransmissionV111Server.

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

  Module ErrorMessage.

    (** Error Message *)
    Record t := {
      error_code : list byte;
      error_msg : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (error_code record) = 4 /\
      Datatypes.length (error_msg record) = 80.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (error_code record) ++
      encode_bytes 80 (error_msg record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (error_code_value, bytes) =>
          match decode_bytes 80 bytes with
          | None => None
          | Some (error_msg_value, bytes) =>
              Some ({| error_code := error_code_value; error_msg := error_msg_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 84.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ErrorMessage.

  Module StrikePriceInstrumentNegativeWholePair.

    Record t := {
      raw_strike_price_instrument : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_instrument record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_instrument record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_instrument := raw_strike_price_instrument_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceInstrumentNegativeWholePair.

  Module StrikePriceInstrumentNegativeTenPair.

    Record t := {
      raw_strike_price_instrument : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_instrument record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_instrument record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_instrument := raw_strike_price_instrument_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceInstrumentNegativeTenPair.

  Module StrikePriceInstrumentNegativeHundredPair.

    Record t := {
      raw_strike_price_instrument : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_instrument record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_instrument record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_instrument := raw_strike_price_instrument_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceInstrumentNegativeHundredPair.

  Module StrikePriceInstrumentNegativeThousandPair.

    Record t := {
      raw_strike_price_instrument : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_instrument record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_instrument record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_instrument := raw_strike_price_instrument_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceInstrumentNegativeThousandPair.

  Module StrikePriceInstrumentNegativeTenThousandPair.

    Record t := {
      raw_strike_price_instrument : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_instrument record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_instrument record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_instrument := raw_strike_price_instrument_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceInstrumentNegativeTenThousandPair.

  Module StrikePriceInstrumentNegativeHundredThousandPair.

    Record t := {
      raw_strike_price_instrument : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_instrument record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_instrument record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_instrument := raw_strike_price_instrument_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceInstrumentNegativeHundredThousandPair.

  Module StrikePriceInstrumentNegativeMillionPair.

    Record t := {
      raw_strike_price_instrument : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_instrument record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_instrument record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_instrument := raw_strike_price_instrument_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceInstrumentNegativeMillionPair.

  Module StrikePriceInstrumentNumericPair.

    Record t := {
      strike_price_instrument : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price_instrument record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price_instrument record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price_instrument := strike_price_instrument_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceInstrumentNumericPair.

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

  Module NetChangeFutureOptionsTradeMessageNegativeWholePair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsTradeMessageNegativeWholePair.

  Module NetChangeFutureOptionsTradeMessageNegativeTenPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsTradeMessageNegativeTenPair.

  Module NetChangeFutureOptionsTradeMessageNegativeHundredPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsTradeMessageNegativeHundredPair.

  Module NetChangeFutureOptionsTradeMessageNegativeThousandPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsTradeMessageNegativeThousandPair.

  Module NetChangeFutureOptionsTradeMessageNegativeTenThousandPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsTradeMessageNegativeTenThousandPair.

  Module NetChangeFutureOptionsTradeMessageNegativeHundredThousandPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsTradeMessageNegativeHundredThousandPair.

  Module NetChangeFutureOptionsTradeMessageNegativeMillionPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsTradeMessageNegativeMillionPair.

  Module NetChangeFutureOptionsTradeMessageNumericPair.

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

  End NetChangeFutureOptionsTradeMessageNumericPair.

  Module NetChangeFuturesTradeMessageNegativeWholePair.

    Record t := {
      raw_net_change_futures_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_trade_message := raw_net_change_futures_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesTradeMessageNegativeWholePair.

  Module NetChangeFuturesTradeMessageNegativeTenPair.

    Record t := {
      raw_net_change_futures_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_trade_message := raw_net_change_futures_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesTradeMessageNegativeTenPair.

  Module NetChangeFuturesTradeMessageNegativeHundredPair.

    Record t := {
      raw_net_change_futures_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_trade_message := raw_net_change_futures_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesTradeMessageNegativeHundredPair.

  Module NetChangeFuturesTradeMessageNegativeThousandPair.

    Record t := {
      raw_net_change_futures_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_trade_message := raw_net_change_futures_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesTradeMessageNegativeThousandPair.

  Module NetChangeFuturesTradeMessageNegativeTenThousandPair.

    Record t := {
      raw_net_change_futures_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_trade_message := raw_net_change_futures_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesTradeMessageNegativeTenThousandPair.

  Module NetChangeFuturesTradeMessageNegativeHundredThousandPair.

    Record t := {
      raw_net_change_futures_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_trade_message := raw_net_change_futures_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesTradeMessageNegativeHundredThousandPair.

  Module NetChangeFuturesTradeMessageNegativeMillionPair.

    Record t := {
      raw_net_change_futures_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_trade_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_trade_message := raw_net_change_futures_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesTradeMessageNegativeMillionPair.

  Module NetChangeFuturesTradeMessageNumericPair.

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

  End NetChangeFuturesTradeMessageNumericPair.

  Module FixedRateNegativeWholePair.

    Record t := {
      raw_fixed_rate : list byte;
      fixed_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_fixed_rate record) = 5 /\
      Datatypes.length (fixed_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (raw_fixed_rate record) ++
      encode_bytes 1 (fixed_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (raw_fixed_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixed_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_fixed_rate := raw_fixed_rate_value; fixed_rate_fraction_indicator := fixed_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedRateNegativeWholePair.

  Module FixedRateNegativeTenPair.

    Record t := {
      raw_fixed_rate : list byte;
      fixed_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_fixed_rate record) = 5 /\
      Datatypes.length (fixed_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (raw_fixed_rate record) ++
      encode_bytes 1 (fixed_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (raw_fixed_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixed_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_fixed_rate := raw_fixed_rate_value; fixed_rate_fraction_indicator := fixed_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedRateNegativeTenPair.

  Module FixedRateNegativeHundredPair.

    Record t := {
      raw_fixed_rate : list byte;
      fixed_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_fixed_rate record) = 5 /\
      Datatypes.length (fixed_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (raw_fixed_rate record) ++
      encode_bytes 1 (fixed_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (raw_fixed_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixed_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_fixed_rate := raw_fixed_rate_value; fixed_rate_fraction_indicator := fixed_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedRateNegativeHundredPair.

  Module FixedRateNegativeThousandPair.

    Record t := {
      raw_fixed_rate : list byte;
      fixed_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_fixed_rate record) = 5 /\
      Datatypes.length (fixed_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (raw_fixed_rate record) ++
      encode_bytes 1 (fixed_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (raw_fixed_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixed_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_fixed_rate := raw_fixed_rate_value; fixed_rate_fraction_indicator := fixed_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedRateNegativeThousandPair.

  Module FixedRateNegativeTenThousandPair.

    Record t := {
      raw_fixed_rate : list byte;
      fixed_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_fixed_rate record) = 5 /\
      Datatypes.length (fixed_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (raw_fixed_rate record) ++
      encode_bytes 1 (fixed_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (raw_fixed_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixed_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_fixed_rate := raw_fixed_rate_value; fixed_rate_fraction_indicator := fixed_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedRateNegativeTenThousandPair.

  Module FixedRateNegativeHundredThousandPair.

    Record t := {
      raw_fixed_rate : list byte;
      fixed_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_fixed_rate record) = 5 /\
      Datatypes.length (fixed_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (raw_fixed_rate record) ++
      encode_bytes 1 (fixed_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (raw_fixed_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixed_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_fixed_rate := raw_fixed_rate_value; fixed_rate_fraction_indicator := fixed_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedRateNegativeHundredThousandPair.

  Module FixedRateNegativeMillionPair.

    Record t := {
      raw_fixed_rate : list byte;
      fixed_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_fixed_rate record) = 5 /\
      Datatypes.length (fixed_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (raw_fixed_rate record) ++
      encode_bytes 1 (fixed_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (raw_fixed_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixed_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_fixed_rate := raw_fixed_rate_value; fixed_rate_fraction_indicator := fixed_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedRateNegativeMillionPair.

  Module FixedRateNumericPair.

    Record t := {
      fixed_rate : list byte;
      fixed_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (fixed_rate record) = 5 /\
      Datatypes.length (fixed_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (fixed_rate record) ++
      encode_bytes 1 (fixed_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (fixed_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (fixed_rate_fraction_indicator_value, bytes) =>
              Some ({| fixed_rate := fixed_rate_value; fixed_rate_fraction_indicator := fixed_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FixedRateNumericPair.

  Module FuturesRfqMessage.

    (** Futures Request for Quote message *)
    Record t := {
      exchange_id : list byte;
      root_symbol : list byte;
      delivery_month : list byte;
      delivery_year_futures : list byte;
      delivery_day : list byte;
      requested_size : list byte;
      requested_market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (root_symbol record) = 6 /\
      Datatypes.length (delivery_month record) = 1 /\
      Datatypes.length (delivery_year_futures record) = 2 /\
      Datatypes.length (delivery_day record) = 2 /\
      Datatypes.length (requested_size record) = 8 /\
      Datatypes.length (requested_market_side record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (root_symbol record) ++
      encode_bytes 1 (delivery_month record) ++
      encode_bytes 2 (delivery_year_futures record) ++
      encode_bytes 2 (delivery_day record) ++
      encode_bytes 8 (requested_size record) ++
      encode_bytes 1 (requested_market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (root_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (delivery_month_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (delivery_year_futures_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (delivery_day_value, bytes) =>
                          match decode_bytes 8 bytes with
                          | None => None
                          | Some (requested_size_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (requested_market_side_value, bytes) =>
                                  Some ({| exchange_id := exchange_id_value; root_symbol := root_symbol_value; delivery_month := delivery_month_value; delivery_year_futures := delivery_year_futures_value; delivery_day := delivery_day_value; requested_size := requested_size_value; requested_market_side := requested_market_side_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End FuturesRfqMessage.

  Module StrategyRfqMessage.

    (** Strategy Request for Quote message *)
    Record t := {
      exchange_id : list byte;
      symbol : list byte;
      requested_size : list byte;
      requested_market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (requested_size record) = 8 /\
      Datatypes.length (requested_market_side record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 8 (requested_size record) ++
      encode_bytes 1 (requested_market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (requested_size_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (requested_market_side_value, bytes) =>
                      Some ({| exchange_id := exchange_id_value; symbol := symbol_value; requested_size := requested_size_value; requested_market_side := requested_market_side_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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

  End StrategyRfqMessage.

  Module StrikePriceScheduleNoticeNegativeWholePair.

    Record t := {
      raw_strike_price_schedule_notice : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_schedule_notice record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_schedule_notice record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_schedule_notice_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_schedule_notice := raw_strike_price_schedule_notice_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceScheduleNoticeNegativeWholePair.

  Module StrikePriceScheduleNoticeNegativeTenPair.

    Record t := {
      raw_strike_price_schedule_notice : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_schedule_notice record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_schedule_notice record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_schedule_notice_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_schedule_notice := raw_strike_price_schedule_notice_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceScheduleNoticeNegativeTenPair.

  Module StrikePriceScheduleNoticeNegativeHundredPair.

    Record t := {
      raw_strike_price_schedule_notice : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_schedule_notice record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_schedule_notice record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_schedule_notice_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_schedule_notice := raw_strike_price_schedule_notice_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceScheduleNoticeNegativeHundredPair.

  Module StrikePriceScheduleNoticeNegativeThousandPair.

    Record t := {
      raw_strike_price_schedule_notice : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_schedule_notice record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_schedule_notice record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_schedule_notice_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_schedule_notice := raw_strike_price_schedule_notice_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceScheduleNoticeNegativeThousandPair.

  Module StrikePriceScheduleNoticeNegativeTenThousandPair.

    Record t := {
      raw_strike_price_schedule_notice : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_schedule_notice record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_schedule_notice record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_schedule_notice_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_schedule_notice := raw_strike_price_schedule_notice_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceScheduleNoticeNegativeTenThousandPair.

  Module StrikePriceScheduleNoticeNegativeHundredThousandPair.

    Record t := {
      raw_strike_price_schedule_notice : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_schedule_notice record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_schedule_notice record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_schedule_notice_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_schedule_notice := raw_strike_price_schedule_notice_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceScheduleNoticeNegativeHundredThousandPair.

  Module StrikePriceScheduleNoticeNegativeMillionPair.

    Record t := {
      raw_strike_price_schedule_notice : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_strike_price_schedule_notice record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_strike_price_schedule_notice record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_strike_price_schedule_notice_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| raw_strike_price_schedule_notice := raw_strike_price_schedule_notice_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceScheduleNoticeNegativeMillionPair.

  Module StrikePriceScheduleNoticeNumericPair.

    Record t := {
      strike_price_schedule_notice : list byte;
      strike_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (strike_price_schedule_notice record) = 7 /\
      Datatypes.length (strike_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (strike_price_schedule_notice record) ++
      encode_bytes 1 (strike_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (strike_price_schedule_notice_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (strike_price_fraction_indicator_value, bytes) =>
              Some ({| strike_price_schedule_notice := strike_price_schedule_notice_value; strike_price_fraction_indicator := strike_price_fraction_indicator_value |}, bytes)
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

  End StrikePriceScheduleNoticeNumericPair.

  Module InstrumentScheduleNoticeFutureMessage.

    (** Instrument Schedule Notice Future message *)
    Record t := {
      exchange_id : list byte;
      root_symbol : list byte;
      delivery_month : list byte;
      delivery_year_futures : list byte;
      delivery_day : list byte;
      series_status : list byte;
      scheduled_status_change_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (root_symbol record) = 6 /\
      Datatypes.length (delivery_month record) = 1 /\
      Datatypes.length (delivery_year_futures record) = 2 /\
      Datatypes.length (delivery_day record) = 2 /\
      Datatypes.length (series_status record) = 1 /\
      Datatypes.length (scheduled_status_change_time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (root_symbol record) ++
      encode_bytes 1 (delivery_month record) ++
      encode_bytes 2 (delivery_year_futures record) ++
      encode_bytes 2 (delivery_day record) ++
      encode_bytes 1 (series_status record) ++
      encode_bytes 6 (scheduled_status_change_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (root_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (delivery_month_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (delivery_year_futures_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (delivery_day_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (series_status_value, bytes) =>
                              match decode_bytes 6 bytes with
                              | None => None
                              | Some (scheduled_status_change_time_value, bytes) =>
                                  Some ({| exchange_id := exchange_id_value; root_symbol := root_symbol_value; delivery_month := delivery_month_value; delivery_year_futures := delivery_year_futures_value; delivery_day := delivery_day_value; series_status := series_status_value; scheduled_status_change_time := scheduled_status_change_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  End InstrumentScheduleNoticeFutureMessage.

  Module InstrumentScheduleNoticeStrategyMessage.

    (** Instrument Schedule Notice Strategy message *)
    Record t := {
      exchange_id : list byte;
      strategy_symbol : list byte;
      series_status : list byte;
      scheduled_status_change_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (strategy_symbol record) = 30 /\
      Datatypes.length (series_status record) = 1 /\
      Datatypes.length (scheduled_status_change_time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (strategy_symbol record) ++
      encode_bytes 1 (series_status record) ++
      encode_bytes 6 (scheduled_status_change_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (strategy_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (series_status_value, bytes) =>
                  match decode_bytes 6 bytes with
                  | None => None
                  | Some (scheduled_status_change_time_value, bytes) =>
                      Some ({| exchange_id := exchange_id_value; strategy_symbol := strategy_symbol_value; series_status := series_status_value; scheduled_status_change_time := scheduled_status_change_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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

  End InstrumentScheduleNoticeStrategyMessage.

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

  Module BidPriceQuoteNumericNegativeWholePair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericNegativeWholePair.

  Module BidPriceQuoteNumericNegativeTenPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericNegativeTenPair.

  Module BidPriceQuoteNumericNegativeHundredPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericNegativeHundredPair.

  Module BidPriceQuoteNumericNegativeThousandPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericNegativeThousandPair.

  Module BidPriceQuoteNumericNegativeTenThousandPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericNegativeTenThousandPair.

  Module BidPriceQuoteNumericNegativeHundredThousandPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericNegativeHundredThousandPair.

  Module BidPriceQuoteNumericNegativeMillionPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericNegativeMillionPair.

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

  Module AskPriceQuoteNumericNegativeWholePair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericNegativeWholePair.

  Module AskPriceQuoteNumericNegativeTenPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericNegativeTenPair.

  Module AskPriceQuoteNumericNegativeHundredPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericNegativeHundredPair.

  Module AskPriceQuoteNumericNegativeThousandPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericNegativeThousandPair.

  Module AskPriceQuoteNumericNegativeTenThousandPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericNegativeTenThousandPair.

  Module AskPriceQuoteNumericNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericNegativeHundredThousandPair.

  Module AskPriceQuoteNumericNegativeMillionPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericNegativeMillionPair.

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

  Module BidPriceQuoteFuturesQuoteMessageOpeningPair.

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

  End BidPriceQuoteFuturesQuoteMessageOpeningPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeWholePair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeWholePair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeTenPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeTenPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeHundredPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeHundredPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeTenThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeTenThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeHundredThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeHundredThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeMillionPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesQuoteMessageNumericPairNegativeMillionPair.

  Module BidPriceQuoteFuturesQuoteMessageNumericPair.

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

  End BidPriceQuoteFuturesQuoteMessageNumericPair.

  Module AskPriceQuoteFuturesQuoteMessageOpeningPair.

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

  End AskPriceQuoteFuturesQuoteMessageOpeningPair.

  Module AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeWholePair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeWholePair.

  Module AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeTenPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeTenPair.

  Module AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeHundredPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeHundredPair.

  Module AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeThousandPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeThousandPair.

  Module AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeTenThousandPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeTenThousandPair.

  Module AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeHundredThousandPair.

  Module AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeMillionPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_futures_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteFuturesQuoteMessageNumericPairNegativeMillionPair.

  Module AskPriceQuoteFuturesQuoteMessageNumericPair.

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

  End AskPriceQuoteFuturesQuoteMessageNumericPair.

  Module BidPriceQuoteStrategyQuoteMessageOpeningPair.

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

  End BidPriceQuoteStrategyQuoteMessageOpeningPair.

  Module BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeWholePair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeWholePair.

  Module BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeTenPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeTenPair.

  Module BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeHundredPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeHundredPair.

  Module BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeTenThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeTenThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeHundredThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeHundredThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeMillionPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_strategy_quote_message_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteStrategyQuoteMessageNumericPairNegativeMillionPair.

  Module BidPriceQuoteStrategyQuoteMessageNumericPair.

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

  End BidPriceQuoteStrategyQuoteMessageNumericPair.

  Module AskPriceQuoteStrategyQuoteMessageOpeningPair.

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

  End AskPriceQuoteStrategyQuoteMessageOpeningPair.

  Module AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeWholePair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeWholePair.

  Module AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeTenPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeTenPair.

  Module AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeHundredPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeHundredPair.

  Module AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeThousandPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeThousandPair.

  Module AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeTenThousandPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeTenThousandPair.

  Module AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeHundredThousandPair.

  Module AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeMillionPair.

    Record t := {
      raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair := raw_ask_price_quote_numeric_ask_price_quote_strategy_quote_message_numeric_pair_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceQuoteNumericAskPriceQuoteStrategyQuoteMessageNumericPairNegativeMillionPair.

  Module AskPriceQuoteStrategyQuoteMessageNumericPair.

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

  End AskPriceQuoteStrategyQuoteMessageNumericPair.

  Module BidPriceQuoteFuturesMarketDepthTradingInstrumentOpeningPair.

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

  End BidPriceQuoteFuturesMarketDepthTradingInstrumentOpeningPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeWholePair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeWholePair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeTenPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeTenPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeHundredPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeHundredPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeTenThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeTenThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeHundredThousandPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeHundredThousandPair.

  Module BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeMillionPair.

    Record t := {
      raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair := raw_bid_price_quote_numeric_bid_price_quote_futures_market_depth_trading_instrument_numeric_pair_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceQuoteNumericBidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPairNegativeMillionPair.

  Module BidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPair.

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

  End BidPriceQuoteFuturesMarketDepthTradingInstrumentNumericPair.

  Module AskPriceFuturesDepthFuturesMarketDepthTradingInstrumentOpeningPair.

    Record t := {
      ask_price_futures_depth_opening : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_futures_depth_opening record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_futures_depth_opening record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_futures_depth_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_futures_depth_opening := ask_price_futures_depth_opening_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthFuturesMarketDepthTradingInstrumentOpeningPair.

  Module AskPriceFuturesDepthNumericNegativeWholePair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthNumericNegativeWholePair.

  Module AskPriceFuturesDepthNumericNegativeTenPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthNumericNegativeTenPair.

  Module AskPriceFuturesDepthNumericNegativeHundredPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthNumericNegativeHundredPair.

  Module AskPriceFuturesDepthNumericNegativeThousandPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthNumericNegativeThousandPair.

  Module AskPriceFuturesDepthNumericNegativeTenThousandPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthNumericNegativeTenThousandPair.

  Module AskPriceFuturesDepthNumericNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthNumericNegativeHundredThousandPair.

  Module AskPriceFuturesDepthNumericNegativeMillionPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthNumericNegativeMillionPair.

  Module AskPriceFuturesDepthFuturesMarketDepthTradingInstrumentNumericPair.

    Record t := {
      ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_futures_depth_numeric record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_futures_depth_numeric := ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceFuturesDepthFuturesMarketDepthTradingInstrumentNumericPair.

  Module PriceNegativeWholePair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 6 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceNegativeWholePair.

  Module PriceNegativeTenPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 6 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceNegativeTenPair.

  Module PriceNegativeHundredPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 6 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceNegativeHundredPair.

  Module PriceNegativeThousandPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 6 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceNegativeThousandPair.

  Module PriceNegativeTenThousandPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 6 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceNegativeTenThousandPair.

  Module PriceNegativeHundredThousandPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 6 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceNegativeHundredThousandPair.

  Module PriceNegativeMillionPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 6 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceNegativeMillionPair.

  Module PriceNumericPair.

    Record t := {
      price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (price record) = 6 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| price := price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceNumericPair.

  Module MaximumThresholdPriceOptionsNegativeWholePair.

    Record t := {
      raw_maximum_threshold_price_options : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_options record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_options record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_options := raw_maximum_threshold_price_options_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceOptionsNegativeWholePair.

  Module MaximumThresholdPriceOptionsNegativeTenPair.

    Record t := {
      raw_maximum_threshold_price_options : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_options record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_options record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_options := raw_maximum_threshold_price_options_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceOptionsNegativeTenPair.

  Module MaximumThresholdPriceOptionsNegativeHundredPair.

    Record t := {
      raw_maximum_threshold_price_options : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_options record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_options record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_options := raw_maximum_threshold_price_options_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceOptionsNegativeHundredPair.

  Module MaximumThresholdPriceOptionsNegativeThousandPair.

    Record t := {
      raw_maximum_threshold_price_options : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_options record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_options record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_options := raw_maximum_threshold_price_options_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceOptionsNegativeThousandPair.

  Module MaximumThresholdPriceOptionsNegativeTenThousandPair.

    Record t := {
      raw_maximum_threshold_price_options : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_options record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_options record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_options := raw_maximum_threshold_price_options_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceOptionsNegativeTenThousandPair.

  Module MaximumThresholdPriceOptionsNegativeHundredThousandPair.

    Record t := {
      raw_maximum_threshold_price_options : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_options record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_options record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_options := raw_maximum_threshold_price_options_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceOptionsNegativeHundredThousandPair.

  Module MaximumThresholdPriceOptionsNegativeMillionPair.

    Record t := {
      raw_maximum_threshold_price_options : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_options record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_options record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_options := raw_maximum_threshold_price_options_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceOptionsNegativeMillionPair.

  Module MaximumThresholdPriceOptionsNumericPair.

    Record t := {
      maximum_threshold_price_options : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (maximum_threshold_price_options record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (maximum_threshold_price_options record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (maximum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| maximum_threshold_price_options := maximum_threshold_price_options_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceOptionsNumericPair.

  Module MinimumThresholdPriceOptionsNegativeWholePair.

    Record t := {
      raw_minimum_threshold_price_options : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_options record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_options record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_options := raw_minimum_threshold_price_options_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceOptionsNegativeWholePair.

  Module MinimumThresholdPriceOptionsNegativeTenPair.

    Record t := {
      raw_minimum_threshold_price_options : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_options record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_options record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_options := raw_minimum_threshold_price_options_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceOptionsNegativeTenPair.

  Module MinimumThresholdPriceOptionsNegativeHundredPair.

    Record t := {
      raw_minimum_threshold_price_options : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_options record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_options record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_options := raw_minimum_threshold_price_options_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceOptionsNegativeHundredPair.

  Module MinimumThresholdPriceOptionsNegativeThousandPair.

    Record t := {
      raw_minimum_threshold_price_options : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_options record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_options record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_options := raw_minimum_threshold_price_options_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceOptionsNegativeThousandPair.

  Module MinimumThresholdPriceOptionsNegativeTenThousandPair.

    Record t := {
      raw_minimum_threshold_price_options : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_options record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_options record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_options := raw_minimum_threshold_price_options_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceOptionsNegativeTenThousandPair.

  Module MinimumThresholdPriceOptionsNegativeHundredThousandPair.

    Record t := {
      raw_minimum_threshold_price_options : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_options record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_options record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_options := raw_minimum_threshold_price_options_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceOptionsNegativeHundredThousandPair.

  Module MinimumThresholdPriceOptionsNegativeMillionPair.

    Record t := {
      raw_minimum_threshold_price_options : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_options record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_options record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_options := raw_minimum_threshold_price_options_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceOptionsNegativeMillionPair.

  Module MinimumThresholdPriceOptionsNumericPair.

    Record t := {
      minimum_threshold_price_options : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (minimum_threshold_price_options record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (minimum_threshold_price_options record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (minimum_threshold_price_options_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| minimum_threshold_price_options := minimum_threshold_price_options_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceOptionsNumericPair.

  Module TickIncrementNumericPair.

    Record t := {
      tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_increment_numeric record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| tick_increment_numeric := tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
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

  Module TickIncrementNumericNegativeWholePair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickIncrementNumericNegativeWholePair.

  Module TickIncrementNumericNegativeTenPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickIncrementNumericNegativeTenPair.

  Module TickIncrementNumericNegativeHundredPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickIncrementNumericNegativeHundredPair.

  Module TickIncrementNumericNegativeThousandPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickIncrementNumericNegativeThousandPair.

  Module TickIncrementNumericNegativeTenThousandPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickIncrementNumericNegativeTenThousandPair.

  Module TickIncrementNumericNegativeHundredThousandPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickIncrementNumericNegativeHundredThousandPair.

  Module TickIncrementNumericNegativeMillionPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickIncrementNumericNegativeMillionPair.

  Module TickIncrementRawPair.

    Record t := {
      tick_increment_raw : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_increment_raw record) = 6 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (tick_increment_raw record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (tick_increment_raw_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| tick_increment_raw := tick_increment_raw_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickIncrementRawPair.

  Module TickValueNegativeWholePair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 6 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickValueNegativeWholePair.

  Module TickValueNegativeTenPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 6 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickValueNegativeTenPair.

  Module TickValueNegativeHundredPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 6 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickValueNegativeHundredPair.

  Module TickValueNegativeThousandPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 6 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickValueNegativeThousandPair.

  Module TickValueNegativeTenThousandPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 6 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickValueNegativeTenThousandPair.

  Module TickValueNegativeHundredThousandPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 6 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickValueNegativeHundredThousandPair.

  Module TickValueNegativeMillionPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 6 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickValueNegativeMillionPair.

  Module TickValueNumericPair.

    Record t := {
      tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_value record) = 6 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| tick_value := tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickValueNumericPair.

  Module UnderlyingInstrumentKeysMessage.

    (** Underlying Instrument Keys message *)
    Record t := {
      exchange_id : list byte;
      group_instrument : list byte;
      instrument : list byte;
      instrument_external_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (group_instrument record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (instrument_external_code record) = 30.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 2 (group_instrument record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 30 (instrument_external_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_instrument_value, bytes) =>
              match decode_bytes 4 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (instrument_external_code_value, bytes) =>
                      Some ({| exchange_id := exchange_id_value; group_instrument := group_instrument_value; instrument := instrument_value; instrument_external_code := instrument_external_code_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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

  End UnderlyingInstrumentKeysMessage.

  Module MaximumThresholdPriceFuturesNegativeWholePair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceFuturesNegativeWholePair.

  Module MaximumThresholdPriceFuturesNegativeTenPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceFuturesNegativeTenPair.

  Module MaximumThresholdPriceFuturesNegativeHundredPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceFuturesNegativeHundredPair.

  Module MaximumThresholdPriceFuturesNegativeThousandPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceFuturesNegativeThousandPair.

  Module MaximumThresholdPriceFuturesNegativeTenThousandPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceFuturesNegativeTenThousandPair.

  Module MaximumThresholdPriceFuturesNegativeHundredThousandPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceFuturesNegativeHundredThousandPair.

  Module MaximumThresholdPriceFuturesNegativeMillionPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceFuturesNegativeMillionPair.

  Module MaximumThresholdPriceFuturesNumericPair.

    Record t := {
      maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (maximum_threshold_price_futures record) = 6 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| maximum_threshold_price_futures := maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MaximumThresholdPriceFuturesNumericPair.

  Module MinimumThresholdPriceFuturesNegativeWholePair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceFuturesNegativeWholePair.

  Module MinimumThresholdPriceFuturesNegativeTenPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceFuturesNegativeTenPair.

  Module MinimumThresholdPriceFuturesNegativeHundredPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceFuturesNegativeHundredPair.

  Module MinimumThresholdPriceFuturesNegativeThousandPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceFuturesNegativeThousandPair.

  Module MinimumThresholdPriceFuturesNegativeTenThousandPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceFuturesNegativeTenThousandPair.

  Module MinimumThresholdPriceFuturesNegativeHundredThousandPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceFuturesNegativeHundredThousandPair.

  Module MinimumThresholdPriceFuturesNegativeMillionPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceFuturesNegativeMillionPair.

  Module MinimumThresholdPriceFuturesNumericPair.

    Record t := {
      minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (minimum_threshold_price_futures record) = 6 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| minimum_threshold_price_futures := minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceFuturesNumericPair.

  Module NotionalPrincipalAmountNegativeWholePair.

    Record t := {
      raw_notional_principal_amount : list byte;
      notional_principal_amount_faction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_notional_principal_amount record) = 8 /\
      Datatypes.length (notional_principal_amount_faction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (raw_notional_principal_amount record) ++
      encode_bytes 1 (notional_principal_amount_faction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (raw_notional_principal_amount_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (notional_principal_amount_faction_indicator_value, bytes) =>
              Some ({| raw_notional_principal_amount := raw_notional_principal_amount_value; notional_principal_amount_faction_indicator := notional_principal_amount_faction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotionalPrincipalAmountNegativeWholePair.

  Module NotionalPrincipalAmountNegativeTenPair.

    Record t := {
      raw_notional_principal_amount : list byte;
      notional_principal_amount_faction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_notional_principal_amount record) = 8 /\
      Datatypes.length (notional_principal_amount_faction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (raw_notional_principal_amount record) ++
      encode_bytes 1 (notional_principal_amount_faction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (raw_notional_principal_amount_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (notional_principal_amount_faction_indicator_value, bytes) =>
              Some ({| raw_notional_principal_amount := raw_notional_principal_amount_value; notional_principal_amount_faction_indicator := notional_principal_amount_faction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotionalPrincipalAmountNegativeTenPair.

  Module NotionalPrincipalAmountNegativeHundredPair.

    Record t := {
      raw_notional_principal_amount : list byte;
      notional_principal_amount_faction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_notional_principal_amount record) = 8 /\
      Datatypes.length (notional_principal_amount_faction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (raw_notional_principal_amount record) ++
      encode_bytes 1 (notional_principal_amount_faction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (raw_notional_principal_amount_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (notional_principal_amount_faction_indicator_value, bytes) =>
              Some ({| raw_notional_principal_amount := raw_notional_principal_amount_value; notional_principal_amount_faction_indicator := notional_principal_amount_faction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotionalPrincipalAmountNegativeHundredPair.

  Module NotionalPrincipalAmountNegativeThousandPair.

    Record t := {
      raw_notional_principal_amount : list byte;
      notional_principal_amount_faction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_notional_principal_amount record) = 8 /\
      Datatypes.length (notional_principal_amount_faction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (raw_notional_principal_amount record) ++
      encode_bytes 1 (notional_principal_amount_faction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (raw_notional_principal_amount_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (notional_principal_amount_faction_indicator_value, bytes) =>
              Some ({| raw_notional_principal_amount := raw_notional_principal_amount_value; notional_principal_amount_faction_indicator := notional_principal_amount_faction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotionalPrincipalAmountNegativeThousandPair.

  Module NotionalPrincipalAmountNegativeTenThousandPair.

    Record t := {
      raw_notional_principal_amount : list byte;
      notional_principal_amount_faction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_notional_principal_amount record) = 8 /\
      Datatypes.length (notional_principal_amount_faction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (raw_notional_principal_amount record) ++
      encode_bytes 1 (notional_principal_amount_faction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (raw_notional_principal_amount_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (notional_principal_amount_faction_indicator_value, bytes) =>
              Some ({| raw_notional_principal_amount := raw_notional_principal_amount_value; notional_principal_amount_faction_indicator := notional_principal_amount_faction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotionalPrincipalAmountNegativeTenThousandPair.

  Module NotionalPrincipalAmountNegativeHundredThousandPair.

    Record t := {
      raw_notional_principal_amount : list byte;
      notional_principal_amount_faction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_notional_principal_amount record) = 8 /\
      Datatypes.length (notional_principal_amount_faction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (raw_notional_principal_amount record) ++
      encode_bytes 1 (notional_principal_amount_faction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (raw_notional_principal_amount_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (notional_principal_amount_faction_indicator_value, bytes) =>
              Some ({| raw_notional_principal_amount := raw_notional_principal_amount_value; notional_principal_amount_faction_indicator := notional_principal_amount_faction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotionalPrincipalAmountNegativeHundredThousandPair.

  Module NotionalPrincipalAmountNegativeMillionPair.

    Record t := {
      raw_notional_principal_amount : list byte;
      notional_principal_amount_faction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_notional_principal_amount record) = 8 /\
      Datatypes.length (notional_principal_amount_faction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (raw_notional_principal_amount record) ++
      encode_bytes 1 (notional_principal_amount_faction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (raw_notional_principal_amount_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (notional_principal_amount_faction_indicator_value, bytes) =>
              Some ({| raw_notional_principal_amount := raw_notional_principal_amount_value; notional_principal_amount_faction_indicator := notional_principal_amount_faction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotionalPrincipalAmountNegativeMillionPair.

  Module NotionalPrincipalAmountNumericPair.

    Record t := {
      notional_principal_amount : list byte;
      notional_principal_amount_faction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (notional_principal_amount record) = 8 /\
      Datatypes.length (notional_principal_amount_faction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 8 (notional_principal_amount record) ++
      encode_bytes 1 (notional_principal_amount_faction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 8 bytes with
      | None => None
      | Some (notional_principal_amount_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (notional_principal_amount_faction_indicator_value, bytes) =>
              Some ({| notional_principal_amount := notional_principal_amount_value; notional_principal_amount_faction_indicator := notional_principal_amount_faction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NotionalPrincipalAmountNumericPair.

  Module BidPriceSummaryNegativeWholePair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceSummaryNegativeWholePair.

  Module BidPriceSummaryNegativeTenPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceSummaryNegativeTenPair.

  Module BidPriceSummaryNegativeHundredPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceSummaryNegativeHundredPair.

  Module BidPriceSummaryNegativeThousandPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceSummaryNegativeThousandPair.

  Module BidPriceSummaryNegativeTenThousandPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceSummaryNegativeTenThousandPair.

  Module BidPriceSummaryNegativeHundredThousandPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceSummaryNegativeHundredThousandPair.

  Module BidPriceSummaryNegativeMillionPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceSummaryNegativeMillionPair.

  Module BidPriceSummaryNumericPair.

    Record t := {
      bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_summary record) = 6 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_summary := bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BidPriceSummaryNumericPair.

  Module AskPriceSummaryNegativeWholePair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceSummaryNegativeWholePair.

  Module AskPriceSummaryNegativeTenPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceSummaryNegativeTenPair.

  Module AskPriceSummaryNegativeHundredPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceSummaryNegativeHundredPair.

  Module AskPriceSummaryNegativeThousandPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceSummaryNegativeThousandPair.

  Module AskPriceSummaryNegativeTenThousandPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceSummaryNegativeTenThousandPair.

  Module AskPriceSummaryNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceSummaryNegativeHundredThousandPair.

  Module AskPriceSummaryNegativeMillionPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceSummaryNegativeMillionPair.

  Module AskPriceSummaryNumericPair.

    Record t := {
      ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_summary record) = 6 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_summary := ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AskPriceSummaryNumericPair.

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

  Module SettlementPriceNegativeWholePair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceNegativeWholePair.

  Module SettlementPriceNegativeTenPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceNegativeTenPair.

  Module SettlementPriceNegativeHundredPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceNegativeHundredPair.

  Module SettlementPriceNegativeThousandPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceNegativeThousandPair.

  Module SettlementPriceNegativeTenThousandPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceNegativeTenThousandPair.

  Module SettlementPriceNegativeHundredThousandPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceNegativeHundredThousandPair.

  Module SettlementPriceNegativeMillionPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceNegativeMillionPair.

  Module SettlementPriceNumericPair.

    Record t := {
      settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| settlement_price := settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceNumericPair.

  Module PreviousSettlementPriceNegativeWholePair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 6 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementPriceNegativeWholePair.

  Module PreviousSettlementPriceNegativeTenPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 6 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementPriceNegativeTenPair.

  Module PreviousSettlementPriceNegativeHundredPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 6 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementPriceNegativeHundredPair.

  Module PreviousSettlementPriceNegativeThousandPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 6 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementPriceNegativeThousandPair.

  Module PreviousSettlementPriceNegativeTenThousandPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 6 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementPriceNegativeTenThousandPair.

  Module PreviousSettlementPriceNegativeHundredThousandPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 6 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementPriceNegativeHundredThousandPair.

  Module PreviousSettlementPriceNegativeMillionPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 6 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementPriceNegativeMillionPair.

  Module PreviousSettlementPriceNumericPair.

    Record t := {
      previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (previous_settlement_price record) = 6 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| previous_settlement_price := previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementPriceNumericPair.

  Module LastPriceFutureOptionsSummaryMessageNegativeWholePair.

    Record t := {
      raw_last_price_future_options_summary_message : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price_future_options_summary_message record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price_future_options_summary_message record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price_future_options_summary_message := raw_last_price_future_options_summary_message_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastPriceFutureOptionsSummaryMessageNegativeWholePair.

  Module LastPriceFutureOptionsSummaryMessageNegativeTenPair.

    Record t := {
      raw_last_price_future_options_summary_message : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price_future_options_summary_message record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price_future_options_summary_message record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price_future_options_summary_message := raw_last_price_future_options_summary_message_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastPriceFutureOptionsSummaryMessageNegativeTenPair.

  Module LastPriceFutureOptionsSummaryMessageNegativeHundredPair.

    Record t := {
      raw_last_price_future_options_summary_message : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price_future_options_summary_message record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price_future_options_summary_message record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price_future_options_summary_message := raw_last_price_future_options_summary_message_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastPriceFutureOptionsSummaryMessageNegativeHundredPair.

  Module LastPriceFutureOptionsSummaryMessageNegativeThousandPair.

    Record t := {
      raw_last_price_future_options_summary_message : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price_future_options_summary_message record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price_future_options_summary_message record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price_future_options_summary_message := raw_last_price_future_options_summary_message_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastPriceFutureOptionsSummaryMessageNegativeThousandPair.

  Module LastPriceFutureOptionsSummaryMessageNegativeTenThousandPair.

    Record t := {
      raw_last_price_future_options_summary_message : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price_future_options_summary_message record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price_future_options_summary_message record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price_future_options_summary_message := raw_last_price_future_options_summary_message_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastPriceFutureOptionsSummaryMessageNegativeTenThousandPair.

  Module LastPriceFutureOptionsSummaryMessageNegativeHundredThousandPair.

    Record t := {
      raw_last_price_future_options_summary_message : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price_future_options_summary_message record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price_future_options_summary_message record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price_future_options_summary_message := raw_last_price_future_options_summary_message_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastPriceFutureOptionsSummaryMessageNegativeHundredThousandPair.

  Module LastPriceFutureOptionsSummaryMessageNegativeMillionPair.

    Record t := {
      raw_last_price_future_options_summary_message : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price_future_options_summary_message record) = 6 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_last_price_future_options_summary_message record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_last_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price_future_options_summary_message := raw_last_price_future_options_summary_message_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LastPriceFutureOptionsSummaryMessageNegativeMillionPair.

  Module LastPriceFutureOptionsSummaryMessageNumericPair.

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

  End LastPriceFutureOptionsSummaryMessageNumericPair.

  Module NetChangeFutureOptionsSummaryMessageNegativeWholePair.

    Record t := {
      raw_net_change_future_options_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_summary_message := raw_net_change_future_options_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsSummaryMessageNegativeWholePair.

  Module NetChangeFutureOptionsSummaryMessageNegativeTenPair.

    Record t := {
      raw_net_change_future_options_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_summary_message := raw_net_change_future_options_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsSummaryMessageNegativeTenPair.

  Module NetChangeFutureOptionsSummaryMessageNegativeHundredPair.

    Record t := {
      raw_net_change_future_options_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_summary_message := raw_net_change_future_options_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsSummaryMessageNegativeHundredPair.

  Module NetChangeFutureOptionsSummaryMessageNegativeThousandPair.

    Record t := {
      raw_net_change_future_options_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_summary_message := raw_net_change_future_options_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsSummaryMessageNegativeThousandPair.

  Module NetChangeFutureOptionsSummaryMessageNegativeTenThousandPair.

    Record t := {
      raw_net_change_future_options_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_summary_message := raw_net_change_future_options_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsSummaryMessageNegativeTenThousandPair.

  Module NetChangeFutureOptionsSummaryMessageNegativeHundredThousandPair.

    Record t := {
      raw_net_change_future_options_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_summary_message := raw_net_change_future_options_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsSummaryMessageNegativeHundredThousandPair.

  Module NetChangeFutureOptionsSummaryMessageNegativeMillionPair.

    Record t := {
      raw_net_change_future_options_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_future_options_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_summary_message := raw_net_change_future_options_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFutureOptionsSummaryMessageNegativeMillionPair.

  Module NetChangeFutureOptionsSummaryMessageNumericPair.

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

  End NetChangeFutureOptionsSummaryMessageNumericPair.

  Module OpeningPriceNegativeWholePair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 6 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningPriceNegativeWholePair.

  Module OpeningPriceNegativeTenPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 6 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningPriceNegativeTenPair.

  Module OpeningPriceNegativeHundredPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 6 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningPriceNegativeHundredPair.

  Module OpeningPriceNegativeThousandPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 6 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningPriceNegativeThousandPair.

  Module OpeningPriceNegativeTenThousandPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 6 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningPriceNegativeTenThousandPair.

  Module OpeningPriceNegativeHundredThousandPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 6 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningPriceNegativeHundredThousandPair.

  Module OpeningPriceNegativeMillionPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 6 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningPriceNegativeMillionPair.

  Module OpeningPriceNumericPair.

    Record t := {
      opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (opening_price record) = 6 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| opening_price := opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningPriceNumericPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeWholePair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceFutureOptionsSummaryMessageNegativeWholePair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeTenPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceFutureOptionsSummaryMessageNegativeTenPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeHundredPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceFutureOptionsSummaryMessageNegativeHundredPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeThousandPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceFutureOptionsSummaryMessageNegativeThousandPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeTenThousandPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceFutureOptionsSummaryMessageNegativeTenThousandPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeHundredThousandPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceFutureOptionsSummaryMessageNegativeHundredThousandPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeMillionPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceFutureOptionsSummaryMessageNegativeMillionPair.

  Module SettlementPriceFutureOptionsSummaryMessageNumericPair.

    Record t := {
      settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_price record) = 6 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| settlement_price := settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SettlementPriceFutureOptionsSummaryMessageNumericPair.

  Module NetChangeFuturesSummaryMessageNegativeWholePair.

    Record t := {
      raw_net_change_futures_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_summary_message := raw_net_change_futures_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesSummaryMessageNegativeWholePair.

  Module NetChangeFuturesSummaryMessageNegativeTenPair.

    Record t := {
      raw_net_change_futures_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_summary_message := raw_net_change_futures_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesSummaryMessageNegativeTenPair.

  Module NetChangeFuturesSummaryMessageNegativeHundredPair.

    Record t := {
      raw_net_change_futures_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_summary_message := raw_net_change_futures_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesSummaryMessageNegativeHundredPair.

  Module NetChangeFuturesSummaryMessageNegativeThousandPair.

    Record t := {
      raw_net_change_futures_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_summary_message := raw_net_change_futures_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesSummaryMessageNegativeThousandPair.

  Module NetChangeFuturesSummaryMessageNegativeTenThousandPair.

    Record t := {
      raw_net_change_futures_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_summary_message := raw_net_change_futures_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesSummaryMessageNegativeTenThousandPair.

  Module NetChangeFuturesSummaryMessageNegativeHundredThousandPair.

    Record t := {
      raw_net_change_futures_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_summary_message := raw_net_change_futures_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesSummaryMessageNegativeHundredThousandPair.

  Module NetChangeFuturesSummaryMessageNegativeMillionPair.

    Record t := {
      raw_net_change_futures_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_futures_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_futures_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_futures_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_futures_summary_message := raw_net_change_futures_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeFuturesSummaryMessageNegativeMillionPair.

  Module NetChangeFuturesSummaryMessageNumericPair.

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

  End NetChangeFuturesSummaryMessageNumericPair.

  Module PreviousSettlementNegativeWholePair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 6 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementNegativeWholePair.

  Module PreviousSettlementNegativeTenPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 6 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementNegativeTenPair.

  Module PreviousSettlementNegativeHundredPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 6 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementNegativeHundredPair.

  Module PreviousSettlementNegativeThousandPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 6 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementNegativeThousandPair.

  Module PreviousSettlementNegativeTenThousandPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 6 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementNegativeTenThousandPair.

  Module PreviousSettlementNegativeHundredThousandPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 6 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementNegativeHundredThousandPair.

  Module PreviousSettlementNegativeMillionPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 6 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementNegativeMillionPair.

  Module PreviousSettlementNumericPair.

    Record t := {
      previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (previous_settlement record) = 6 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| previous_settlement := previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousSettlementNumericPair.

  Module ExternalPriceAtSourceNegativeWholePair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 6 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalPriceAtSourceNegativeWholePair.

  Module ExternalPriceAtSourceNegativeTenPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 6 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalPriceAtSourceNegativeTenPair.

  Module ExternalPriceAtSourceNegativeHundredPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 6 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalPriceAtSourceNegativeHundredPair.

  Module ExternalPriceAtSourceNegativeThousandPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 6 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalPriceAtSourceNegativeThousandPair.

  Module ExternalPriceAtSourceNegativeTenThousandPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 6 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalPriceAtSourceNegativeTenThousandPair.

  Module ExternalPriceAtSourceNegativeHundredThousandPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 6 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalPriceAtSourceNegativeHundredThousandPair.

  Module ExternalPriceAtSourceNegativeMillionPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 6 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalPriceAtSourceNegativeMillionPair.

  Module ExternalPriceAtSourceNumericPair.

    Record t := {
      external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (external_price_at_source record) = 6 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| external_price_at_source := external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExternalPriceAtSourceNumericPair.

  Module NetChangeStrategySummaryMessageNegativeWholePair.

    Record t := {
      raw_net_change_strategy_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_strategy_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_strategy_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_strategy_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_strategy_summary_message := raw_net_change_strategy_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeStrategySummaryMessageNegativeWholePair.

  Module NetChangeStrategySummaryMessageNegativeTenPair.

    Record t := {
      raw_net_change_strategy_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_strategy_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_strategy_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_strategy_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_strategy_summary_message := raw_net_change_strategy_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeStrategySummaryMessageNegativeTenPair.

  Module NetChangeStrategySummaryMessageNegativeHundredPair.

    Record t := {
      raw_net_change_strategy_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_strategy_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_strategy_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_strategy_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_strategy_summary_message := raw_net_change_strategy_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeStrategySummaryMessageNegativeHundredPair.

  Module NetChangeStrategySummaryMessageNegativeThousandPair.

    Record t := {
      raw_net_change_strategy_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_strategy_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_strategy_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_strategy_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_strategy_summary_message := raw_net_change_strategy_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeStrategySummaryMessageNegativeThousandPair.

  Module NetChangeStrategySummaryMessageNegativeTenThousandPair.

    Record t := {
      raw_net_change_strategy_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_strategy_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_strategy_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_strategy_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_strategy_summary_message := raw_net_change_strategy_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeStrategySummaryMessageNegativeTenThousandPair.

  Module NetChangeStrategySummaryMessageNegativeHundredThousandPair.

    Record t := {
      raw_net_change_strategy_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_strategy_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_strategy_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_strategy_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_strategy_summary_message := raw_net_change_strategy_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeStrategySummaryMessageNegativeHundredThousandPair.

  Module NetChangeStrategySummaryMessageNegativeMillionPair.

    Record t := {
      raw_net_change_strategy_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_strategy_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_strategy_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_strategy_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_strategy_summary_message := raw_net_change_strategy_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeStrategySummaryMessageNegativeMillionPair.

  Module NetChangeStrategySummaryMessageNumericPair.

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

  End NetChangeStrategySummaryMessageNumericPair.

  Module NetPresentValueANegativeWholePair.

    Record t := {
      raw_net_present_value_a : list byte;
      net_present_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_present_value_a record) = 11 /\
      Datatypes.length (net_present_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_net_present_value_a record) ++
      encode_bytes 1 (net_present_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_net_present_value_a_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_present_value_fraction_indicator_value, bytes) =>
              Some ({| raw_net_present_value_a := raw_net_present_value_a_value; net_present_value_fraction_indicator := net_present_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetPresentValueANegativeWholePair.

  Module NetPresentValueANegativeTenPair.

    Record t := {
      raw_net_present_value_a : list byte;
      net_present_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_present_value_a record) = 11 /\
      Datatypes.length (net_present_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_net_present_value_a record) ++
      encode_bytes 1 (net_present_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_net_present_value_a_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_present_value_fraction_indicator_value, bytes) =>
              Some ({| raw_net_present_value_a := raw_net_present_value_a_value; net_present_value_fraction_indicator := net_present_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetPresentValueANegativeTenPair.

  Module NetPresentValueANegativeHundredPair.

    Record t := {
      raw_net_present_value_a : list byte;
      net_present_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_present_value_a record) = 11 /\
      Datatypes.length (net_present_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_net_present_value_a record) ++
      encode_bytes 1 (net_present_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_net_present_value_a_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_present_value_fraction_indicator_value, bytes) =>
              Some ({| raw_net_present_value_a := raw_net_present_value_a_value; net_present_value_fraction_indicator := net_present_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetPresentValueANegativeHundredPair.

  Module NetPresentValueANegativeThousandPair.

    Record t := {
      raw_net_present_value_a : list byte;
      net_present_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_present_value_a record) = 11 /\
      Datatypes.length (net_present_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_net_present_value_a record) ++
      encode_bytes 1 (net_present_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_net_present_value_a_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_present_value_fraction_indicator_value, bytes) =>
              Some ({| raw_net_present_value_a := raw_net_present_value_a_value; net_present_value_fraction_indicator := net_present_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetPresentValueANegativeThousandPair.

  Module NetPresentValueANegativeTenThousandPair.

    Record t := {
      raw_net_present_value_a : list byte;
      net_present_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_present_value_a record) = 11 /\
      Datatypes.length (net_present_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_net_present_value_a record) ++
      encode_bytes 1 (net_present_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_net_present_value_a_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_present_value_fraction_indicator_value, bytes) =>
              Some ({| raw_net_present_value_a := raw_net_present_value_a_value; net_present_value_fraction_indicator := net_present_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetPresentValueANegativeTenThousandPair.

  Module NetPresentValueANegativeHundredThousandPair.

    Record t := {
      raw_net_present_value_a : list byte;
      net_present_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_present_value_a record) = 11 /\
      Datatypes.length (net_present_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_net_present_value_a record) ++
      encode_bytes 1 (net_present_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_net_present_value_a_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_present_value_fraction_indicator_value, bytes) =>
              Some ({| raw_net_present_value_a := raw_net_present_value_a_value; net_present_value_fraction_indicator := net_present_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetPresentValueANegativeHundredThousandPair.

  Module NetPresentValueANegativeMillionPair.

    Record t := {
      raw_net_present_value_a : list byte;
      net_present_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_present_value_a record) = 11 /\
      Datatypes.length (net_present_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_net_present_value_a record) ++
      encode_bytes 1 (net_present_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_net_present_value_a_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_present_value_fraction_indicator_value, bytes) =>
              Some ({| raw_net_present_value_a := raw_net_present_value_a_value; net_present_value_fraction_indicator := net_present_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetPresentValueANegativeMillionPair.

  Module NetPresentValueANumericPair.

    Record t := {
      net_present_value_a : list byte;
      net_present_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (net_present_value_a record) = 11 /\
      Datatypes.length (net_present_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (net_present_value_a record) ++
      encode_bytes 1 (net_present_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (net_present_value_a_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_present_value_fraction_indicator_value, bytes) =>
              Some ({| net_present_value_a := net_present_value_a_value; net_present_value_fraction_indicator := net_present_value_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetPresentValueANumericPair.

  Module HistoricalCouponBNegativeWholePair.

    Record t := {
      raw_historical_coupon_b : list byte;
      historical_coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_historical_coupon_b record) = 11 /\
      Datatypes.length (historical_coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_historical_coupon_b record) ++
      encode_bytes 1 (historical_coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_historical_coupon_b_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (historical_coupon_fraction_indicator_value, bytes) =>
              Some ({| raw_historical_coupon_b := raw_historical_coupon_b_value; historical_coupon_fraction_indicator := historical_coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HistoricalCouponBNegativeWholePair.

  Module HistoricalCouponBNegativeTenPair.

    Record t := {
      raw_historical_coupon_b : list byte;
      historical_coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_historical_coupon_b record) = 11 /\
      Datatypes.length (historical_coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_historical_coupon_b record) ++
      encode_bytes 1 (historical_coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_historical_coupon_b_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (historical_coupon_fraction_indicator_value, bytes) =>
              Some ({| raw_historical_coupon_b := raw_historical_coupon_b_value; historical_coupon_fraction_indicator := historical_coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HistoricalCouponBNegativeTenPair.

  Module HistoricalCouponBNegativeHundredPair.

    Record t := {
      raw_historical_coupon_b : list byte;
      historical_coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_historical_coupon_b record) = 11 /\
      Datatypes.length (historical_coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_historical_coupon_b record) ++
      encode_bytes 1 (historical_coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_historical_coupon_b_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (historical_coupon_fraction_indicator_value, bytes) =>
              Some ({| raw_historical_coupon_b := raw_historical_coupon_b_value; historical_coupon_fraction_indicator := historical_coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HistoricalCouponBNegativeHundredPair.

  Module HistoricalCouponBNegativeThousandPair.

    Record t := {
      raw_historical_coupon_b : list byte;
      historical_coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_historical_coupon_b record) = 11 /\
      Datatypes.length (historical_coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_historical_coupon_b record) ++
      encode_bytes 1 (historical_coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_historical_coupon_b_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (historical_coupon_fraction_indicator_value, bytes) =>
              Some ({| raw_historical_coupon_b := raw_historical_coupon_b_value; historical_coupon_fraction_indicator := historical_coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HistoricalCouponBNegativeThousandPair.

  Module HistoricalCouponBNegativeTenThousandPair.

    Record t := {
      raw_historical_coupon_b : list byte;
      historical_coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_historical_coupon_b record) = 11 /\
      Datatypes.length (historical_coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_historical_coupon_b record) ++
      encode_bytes 1 (historical_coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_historical_coupon_b_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (historical_coupon_fraction_indicator_value, bytes) =>
              Some ({| raw_historical_coupon_b := raw_historical_coupon_b_value; historical_coupon_fraction_indicator := historical_coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HistoricalCouponBNegativeTenThousandPair.

  Module HistoricalCouponBNegativeHundredThousandPair.

    Record t := {
      raw_historical_coupon_b : list byte;
      historical_coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_historical_coupon_b record) = 11 /\
      Datatypes.length (historical_coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_historical_coupon_b record) ++
      encode_bytes 1 (historical_coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_historical_coupon_b_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (historical_coupon_fraction_indicator_value, bytes) =>
              Some ({| raw_historical_coupon_b := raw_historical_coupon_b_value; historical_coupon_fraction_indicator := historical_coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HistoricalCouponBNegativeHundredThousandPair.

  Module HistoricalCouponBNegativeMillionPair.

    Record t := {
      raw_historical_coupon_b : list byte;
      historical_coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_historical_coupon_b record) = 11 /\
      Datatypes.length (historical_coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_historical_coupon_b record) ++
      encode_bytes 1 (historical_coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_historical_coupon_b_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (historical_coupon_fraction_indicator_value, bytes) =>
              Some ({| raw_historical_coupon_b := raw_historical_coupon_b_value; historical_coupon_fraction_indicator := historical_coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HistoricalCouponBNegativeMillionPair.

  Module HistoricalCouponBNumericPair.

    Record t := {
      historical_coupon_b : list byte;
      historical_coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (historical_coupon_b record) = 11 /\
      Datatypes.length (historical_coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (historical_coupon_b record) ++
      encode_bytes 1 (historical_coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (historical_coupon_b_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (historical_coupon_fraction_indicator_value, bytes) =>
              Some ({| historical_coupon_b := historical_coupon_b_value; historical_coupon_fraction_indicator := historical_coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End HistoricalCouponBNumericPair.

  Module PriceAlignmentInterestCNegativeWholePair.

    Record t := {
      raw_price_alignment_interest_c : list byte;
      price_alignment_interest_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price_alignment_interest_c record) = 11 /\
      Datatypes.length (price_alignment_interest_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_price_alignment_interest_c record) ++
      encode_bytes 1 (price_alignment_interest_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_price_alignment_interest_c_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_alignment_interest_fraction_indicator_value, bytes) =>
              Some ({| raw_price_alignment_interest_c := raw_price_alignment_interest_c_value; price_alignment_interest_fraction_indicator := price_alignment_interest_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceAlignmentInterestCNegativeWholePair.

  Module PriceAlignmentInterestCNegativeTenPair.

    Record t := {
      raw_price_alignment_interest_c : list byte;
      price_alignment_interest_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price_alignment_interest_c record) = 11 /\
      Datatypes.length (price_alignment_interest_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_price_alignment_interest_c record) ++
      encode_bytes 1 (price_alignment_interest_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_price_alignment_interest_c_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_alignment_interest_fraction_indicator_value, bytes) =>
              Some ({| raw_price_alignment_interest_c := raw_price_alignment_interest_c_value; price_alignment_interest_fraction_indicator := price_alignment_interest_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceAlignmentInterestCNegativeTenPair.

  Module PriceAlignmentInterestCNegativeHundredPair.

    Record t := {
      raw_price_alignment_interest_c : list byte;
      price_alignment_interest_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price_alignment_interest_c record) = 11 /\
      Datatypes.length (price_alignment_interest_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_price_alignment_interest_c record) ++
      encode_bytes 1 (price_alignment_interest_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_price_alignment_interest_c_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_alignment_interest_fraction_indicator_value, bytes) =>
              Some ({| raw_price_alignment_interest_c := raw_price_alignment_interest_c_value; price_alignment_interest_fraction_indicator := price_alignment_interest_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceAlignmentInterestCNegativeHundredPair.

  Module PriceAlignmentInterestCNegativeThousandPair.

    Record t := {
      raw_price_alignment_interest_c : list byte;
      price_alignment_interest_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price_alignment_interest_c record) = 11 /\
      Datatypes.length (price_alignment_interest_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_price_alignment_interest_c record) ++
      encode_bytes 1 (price_alignment_interest_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_price_alignment_interest_c_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_alignment_interest_fraction_indicator_value, bytes) =>
              Some ({| raw_price_alignment_interest_c := raw_price_alignment_interest_c_value; price_alignment_interest_fraction_indicator := price_alignment_interest_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceAlignmentInterestCNegativeThousandPair.

  Module PriceAlignmentInterestCNegativeTenThousandPair.

    Record t := {
      raw_price_alignment_interest_c : list byte;
      price_alignment_interest_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price_alignment_interest_c record) = 11 /\
      Datatypes.length (price_alignment_interest_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_price_alignment_interest_c record) ++
      encode_bytes 1 (price_alignment_interest_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_price_alignment_interest_c_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_alignment_interest_fraction_indicator_value, bytes) =>
              Some ({| raw_price_alignment_interest_c := raw_price_alignment_interest_c_value; price_alignment_interest_fraction_indicator := price_alignment_interest_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceAlignmentInterestCNegativeTenThousandPair.

  Module PriceAlignmentInterestCNegativeHundredThousandPair.

    Record t := {
      raw_price_alignment_interest_c : list byte;
      price_alignment_interest_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price_alignment_interest_c record) = 11 /\
      Datatypes.length (price_alignment_interest_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_price_alignment_interest_c record) ++
      encode_bytes 1 (price_alignment_interest_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_price_alignment_interest_c_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_alignment_interest_fraction_indicator_value, bytes) =>
              Some ({| raw_price_alignment_interest_c := raw_price_alignment_interest_c_value; price_alignment_interest_fraction_indicator := price_alignment_interest_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceAlignmentInterestCNegativeHundredThousandPair.

  Module PriceAlignmentInterestCNegativeMillionPair.

    Record t := {
      raw_price_alignment_interest_c : list byte;
      price_alignment_interest_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price_alignment_interest_c record) = 11 /\
      Datatypes.length (price_alignment_interest_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (raw_price_alignment_interest_c record) ++
      encode_bytes 1 (price_alignment_interest_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (raw_price_alignment_interest_c_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_alignment_interest_fraction_indicator_value, bytes) =>
              Some ({| raw_price_alignment_interest_c := raw_price_alignment_interest_c_value; price_alignment_interest_fraction_indicator := price_alignment_interest_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceAlignmentInterestCNegativeMillionPair.

  Module PriceAlignmentInterestCNumericPair.

    Record t := {
      price_alignment_interest_c : list byte;
      price_alignment_interest_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (price_alignment_interest_c record) = 11 /\
      Datatypes.length (price_alignment_interest_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 11 (price_alignment_interest_c record) ++
      encode_bytes 1 (price_alignment_interest_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 11 bytes with
      | None => None
      | Some (price_alignment_interest_c_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_alignment_interest_fraction_indicator_value, bytes) =>
              Some ({| price_alignment_interest_c := price_alignment_interest_c_value; price_alignment_interest_fraction_indicator := price_alignment_interest_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PriceAlignmentInterestCNumericPair.

  Module NetChangeSwapFutureSummaryMessageNegativeWholePair.

    Record t := {
      raw_net_change_swap_future_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_swap_future_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_swap_future_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_swap_future_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_swap_future_summary_message := raw_net_change_swap_future_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeSwapFutureSummaryMessageNegativeWholePair.

  Module NetChangeSwapFutureSummaryMessageNegativeTenPair.

    Record t := {
      raw_net_change_swap_future_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_swap_future_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_swap_future_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_swap_future_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_swap_future_summary_message := raw_net_change_swap_future_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeSwapFutureSummaryMessageNegativeTenPair.

  Module NetChangeSwapFutureSummaryMessageNegativeHundredPair.

    Record t := {
      raw_net_change_swap_future_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_swap_future_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_swap_future_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_swap_future_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_swap_future_summary_message := raw_net_change_swap_future_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeSwapFutureSummaryMessageNegativeHundredPair.

  Module NetChangeSwapFutureSummaryMessageNegativeThousandPair.

    Record t := {
      raw_net_change_swap_future_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_swap_future_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_swap_future_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_swap_future_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_swap_future_summary_message := raw_net_change_swap_future_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeSwapFutureSummaryMessageNegativeThousandPair.

  Module NetChangeSwapFutureSummaryMessageNegativeTenThousandPair.

    Record t := {
      raw_net_change_swap_future_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_swap_future_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_swap_future_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_swap_future_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_swap_future_summary_message := raw_net_change_swap_future_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeSwapFutureSummaryMessageNegativeTenThousandPair.

  Module NetChangeSwapFutureSummaryMessageNegativeHundredThousandPair.

    Record t := {
      raw_net_change_swap_future_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_swap_future_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_swap_future_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_swap_future_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_swap_future_summary_message := raw_net_change_swap_future_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeSwapFutureSummaryMessageNegativeHundredThousandPair.

  Module NetChangeSwapFutureSummaryMessageNegativeMillionPair.

    Record t := {
      raw_net_change_swap_future_summary_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_swap_future_summary_message record) = 6 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_net_change_swap_future_summary_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_net_change_swap_future_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_swap_future_summary_message := raw_net_change_swap_future_summary_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NetChangeSwapFutureSummaryMessageNegativeMillionPair.

  Module NetChangeSwapFutureSummaryMessageNumericPair.

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

  End NetChangeSwapFutureSummaryMessageNumericPair.

  Module PreviousResetRateNegativeWholePair.

    Record t := {
      raw_previous_reset_rate : list byte;
      previous_reset_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_reset_rate record) = 6 /\
      Datatypes.length (previous_reset_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_reset_rate record) ++
      encode_bytes 1 (previous_reset_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_reset_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_reset_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_reset_rate := raw_previous_reset_rate_value; previous_reset_rate_fraction_indicator := previous_reset_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousResetRateNegativeWholePair.

  Module PreviousResetRateNegativeTenPair.

    Record t := {
      raw_previous_reset_rate : list byte;
      previous_reset_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_reset_rate record) = 6 /\
      Datatypes.length (previous_reset_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_reset_rate record) ++
      encode_bytes 1 (previous_reset_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_reset_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_reset_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_reset_rate := raw_previous_reset_rate_value; previous_reset_rate_fraction_indicator := previous_reset_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousResetRateNegativeTenPair.

  Module PreviousResetRateNegativeHundredPair.

    Record t := {
      raw_previous_reset_rate : list byte;
      previous_reset_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_reset_rate record) = 6 /\
      Datatypes.length (previous_reset_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_reset_rate record) ++
      encode_bytes 1 (previous_reset_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_reset_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_reset_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_reset_rate := raw_previous_reset_rate_value; previous_reset_rate_fraction_indicator := previous_reset_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousResetRateNegativeHundredPair.

  Module PreviousResetRateNegativeThousandPair.

    Record t := {
      raw_previous_reset_rate : list byte;
      previous_reset_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_reset_rate record) = 6 /\
      Datatypes.length (previous_reset_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_reset_rate record) ++
      encode_bytes 1 (previous_reset_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_reset_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_reset_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_reset_rate := raw_previous_reset_rate_value; previous_reset_rate_fraction_indicator := previous_reset_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousResetRateNegativeThousandPair.

  Module PreviousResetRateNegativeTenThousandPair.

    Record t := {
      raw_previous_reset_rate : list byte;
      previous_reset_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_reset_rate record) = 6 /\
      Datatypes.length (previous_reset_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_reset_rate record) ++
      encode_bytes 1 (previous_reset_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_reset_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_reset_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_reset_rate := raw_previous_reset_rate_value; previous_reset_rate_fraction_indicator := previous_reset_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousResetRateNegativeTenThousandPair.

  Module PreviousResetRateNegativeHundredThousandPair.

    Record t := {
      raw_previous_reset_rate : list byte;
      previous_reset_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_reset_rate record) = 6 /\
      Datatypes.length (previous_reset_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_reset_rate record) ++
      encode_bytes 1 (previous_reset_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_reset_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_reset_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_reset_rate := raw_previous_reset_rate_value; previous_reset_rate_fraction_indicator := previous_reset_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousResetRateNegativeHundredThousandPair.

  Module PreviousResetRateNegativeMillionPair.

    Record t := {
      raw_previous_reset_rate : list byte;
      previous_reset_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_reset_rate record) = 6 /\
      Datatypes.length (previous_reset_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_previous_reset_rate record) ++
      encode_bytes 1 (previous_reset_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_previous_reset_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_reset_rate_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_reset_rate := raw_previous_reset_rate_value; previous_reset_rate_fraction_indicator := previous_reset_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousResetRateNegativeMillionPair.

  Module PreviousResetRateNumericPair.

    Record t := {
      previous_reset_rate : list byte;
      previous_reset_rate_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (previous_reset_rate record) = 6 /\
      Datatypes.length (previous_reset_rate_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (previous_reset_rate record) ++
      encode_bytes 1 (previous_reset_rate_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (previous_reset_rate_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_reset_rate_fraction_indicator_value, bytes) =>
              Some ({| previous_reset_rate := previous_reset_rate_value; previous_reset_rate_fraction_indicator := previous_reset_rate_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousResetRateNumericPair.

  Module BeginningOfOptionsSummaryMessage.

    (** Beginning of Options Summary message *)
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

  Module BeginningOfFutureOptionsSummaryMessage.

    (** Beginning of Future Options Summary message *)
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

  End BeginningOfFutureOptionsSummaryMessage.

  Module BeginningOfFuturesSummaryMessage.

    (** Beginning of Futures Summary message *)
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

  End BeginningOfFuturesSummaryMessage.

  Module BeginningOfStrategySummaryMessage.

    (** Beginning of Strategy Summary message *)
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

  End BeginningOfStrategySummaryMessage.

  Module SwapFutureBeginningOfSummaryMessage.

    (** Swap Future Beginning of Summary message *)
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

  End SwapFutureBeginningOfSummaryMessage.

  Module GroupStatusMessage.

    (** group Status message *)
    Record t := {
      exchange_id : list byte;
      root_symbol_group : list byte;
      group_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (root_symbol_group record) = 6 /\
      Datatypes.length (group_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (root_symbol_group record) ++
      encode_bytes 1 (group_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (root_symbol_group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (group_status_value, bytes) =>
                  Some ({| exchange_id := exchange_id_value; root_symbol_group := root_symbol_group_value; group_status := group_status_value |}, bytes)
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

  Module GroupStatusStrategiesMessage.

    (** Strategies message *)
    Record t := {
      exchange_id : list byte;
      group_instrument : list byte;
      group_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (group_instrument record) = 2 /\
      Datatypes.length (group_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 2 (group_instrument record) ++
      encode_bytes 1 (group_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (group_instrument_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (group_status_value, bytes) =>
                  Some ({| exchange_id := exchange_id_value; group_instrument := group_instrument_value; group_status := group_status_value |}, bytes)
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

  End GroupStatusStrategiesMessage.

  Module RegularTextBulletin.

    Record t := {
      regular_bulletin_contents : list byte;
      continue_marker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (regular_bulletin_contents record) = 79 /\
      Datatypes.length (continue_marker record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 79 (regular_bulletin_contents record) ++
      encode_bytes 1 (continue_marker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 79 bytes with
      | None => None
      | Some (regular_bulletin_contents_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (continue_marker_value, bytes) =>
              Some ({| regular_bulletin_contents := regular_bulletin_contents_value; continue_marker := continue_marker_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RegularTextBulletin.

  Module SpecialTextBulletin.

    (** This bulletin type will be used for bulletins relating to a specific trading instrument. Any continuation records will also contain the symbol as the first 30 bytes of the bulletin field. *)
    Record t := {
      symbol : list byte;
      special_bulletin_contents : list byte;
      continue_marker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (special_bulletin_contents record) = 49 /\
      Datatypes.length (continue_marker record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 30 (symbol record) ++
      encode_bytes 49 (special_bulletin_contents record) ++
      encode_bytes 1 (continue_marker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 30 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 49 bytes with
          | None => None
          | Some (special_bulletin_contents_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (continue_marker_value, bytes) =>
                  Some ({| symbol := symbol_value; special_bulletin_contents := special_bulletin_contents_value; continue_marker := continue_marker_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
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

  End SpecialTextBulletin.

  Module EndOfSalesMessage.

    (** End of Sales message *)
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

  Module MinPriceNegativeWholePair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 6 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinPriceNegativeWholePair.

  Module MinPriceNegativeTenPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 6 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinPriceNegativeTenPair.

  Module MinPriceNegativeHundredPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 6 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinPriceNegativeHundredPair.

  Module MinPriceNegativeThousandPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 6 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinPriceNegativeThousandPair.

  Module MinPriceNegativeTenThousandPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 6 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinPriceNegativeTenThousandPair.

  Module MinPriceNegativeHundredThousandPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 6 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinPriceNegativeHundredThousandPair.

  Module MinPriceNegativeMillionPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 6 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinPriceNegativeMillionPair.

  Module MinPriceNumericPair.

    Record t := {
      min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (min_price record) = 6 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| min_price := min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinPriceNumericPair.

  Module TickPriceNegativeWholePair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 6 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickPriceNegativeWholePair.

  Module TickPriceNegativeTenPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 6 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickPriceNegativeTenPair.

  Module TickPriceNegativeHundredPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 6 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickPriceNegativeHundredPair.

  Module TickPriceNegativeThousandPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 6 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickPriceNegativeThousandPair.

  Module TickPriceNegativeTenThousandPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 6 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickPriceNegativeTenThousandPair.

  Module TickPriceNegativeHundredThousandPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 6 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickPriceNegativeHundredThousandPair.

  Module TickPriceNegativeMillionPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 6 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickPriceNegativeMillionPair.

  Module TickPriceNumericPair.

    Record t := {
      tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_price record) = 6 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| tick_price := tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickPriceNumericPair.

  Module EndOfTransmissionMessage.

    (** End of Transmission message *)
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

    (** Circuit Assurance message *)
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

  Module TimebeatMessage.

    (** This message is sent out every second. *)
    Record t := {
      time_with_milliseconds : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (time_with_milliseconds record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 9 (time_with_milliseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 9 bytes with
      | None => None
      | Some (time_with_milliseconds_value, bytes) =>
          Some ({| time_with_milliseconds := time_with_milliseconds_value |}, bytes)
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

  End TimebeatMessage.

End MxSolaTcpRetransmissionV111Server.
