From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * TMX Group Sola Multicast

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

Module MxSolaMulticastV1122.

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

  Module LongMessageHeader.

    (** The guide states these fields once, as Table 3: Long Message Header, for every message the eight Table 2 frames do not. Sequence Number and Message Type are read by the packet, so they are not repeated here. *)
    Record t := {
      message_timestamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_timestamp record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (message_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (message_timestamp_value, bytes) =>
          Some ({| message_timestamp := message_timestamp_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End LongMessageHeader.

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

  Module TradePriceNegativeWholePair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 7 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeWholePair.

  Module TradePriceNegativeTenPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 7 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenPair.

  Module TradePriceNegativeHundredPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 7 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredPair.

  Module TradePriceNegativeThousandPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 7 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeThousandPair.

  Module TradePriceNegativeTenThousandPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 7 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeTenThousandPair.

  Module TradePriceNegativeHundredThousandPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 7 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeHundredThousandPair.

  Module TradePriceNegativeMillionPair.

    Record t := {
      raw_trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_trade_price record) = 7 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| raw_trade_price := raw_trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNegativeMillionPair.

  Module TradePriceNumericPair.

    Record t := {
      trade_price : list byte;
      trade_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trade_price record) = 7 /\
      Datatypes.length (trade_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (trade_price record) ++
      encode_bytes 1 (trade_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (trade_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (trade_price_fraction_indicator_value, bytes) =>
              Some ({| trade_price := trade_price_value; trade_price_fraction_indicator := trade_price_fraction_indicator_value |}, bytes)
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

  End TradePriceNumericPair.

  Module NetChangeNegativeWholePair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeWholePair.

  Module NetChangeNegativeTenPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenPair.

  Module NetChangeNegativeHundredPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredPair.

  Module NetChangeNegativeThousandPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeThousandPair.

  Module NetChangeNegativeTenThousandPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeTenThousandPair.

  Module NetChangeNegativeHundredThousandPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeHundredThousandPair.

  Module NetChangeNegativeMillionPair.

    Record t := {
      raw_net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change := raw_net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNegativeMillionPair.

  Module NetChangeNumericPair.

    Record t := {
      net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| net_change := net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeNumericPair.

  Module NetChangeFutureOptionsTradeMessageNegativeWholePair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeFutureOptionsTradeMessageNegativeWholePair.

  Module NetChangeFutureOptionsTradeMessageNegativeTenPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeFutureOptionsTradeMessageNegativeTenPair.

  Module NetChangeFutureOptionsTradeMessageNegativeHundredPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeFutureOptionsTradeMessageNegativeHundredPair.

  Module NetChangeFutureOptionsTradeMessageNegativeThousandPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeFutureOptionsTradeMessageNegativeThousandPair.

  Module NetChangeFutureOptionsTradeMessageNegativeTenThousandPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeFutureOptionsTradeMessageNegativeTenThousandPair.

  Module NetChangeFutureOptionsTradeMessageNegativeHundredThousandPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeFutureOptionsTradeMessageNegativeHundredThousandPair.

  Module NetChangeFutureOptionsTradeMessageNegativeMillionPair.

    Record t := {
      raw_net_change_future_options_trade_message : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_net_change_future_options_trade_message record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_net_change_future_options_trade_message record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_net_change_future_options_trade_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| raw_net_change_future_options_trade_message := raw_net_change_future_options_trade_message_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeFutureOptionsTradeMessageNegativeMillionPair.

  Module NetChangeFutureOptionsTradeMessageNumericPair.

    Record t := {
      net_change : list byte;
      net_change_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (net_change record) = 7 /\
      Datatypes.length (net_change_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (net_change record) ++
      encode_bytes 1 (net_change_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (net_change_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (net_change_fraction_indicator_value, bytes) =>
              Some ({| net_change := net_change_value; net_change_fraction_indicator := net_change_fraction_indicator_value |}, bytes)
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

  End NetChangeFutureOptionsTradeMessageNumericPair.

  Module FutureProduct.

    (** The guide states the future product once and every futures message carries it. *)
    Record t := {
      root_symbol : list byte;
      symbol_month : list byte;
      symbol_year : list byte;
      expiry_day : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (root_symbol record) = 6 /\
      Datatypes.length (symbol_month record) = 1 /\
      Datatypes.length (symbol_year record) = 2 /\
      Datatypes.length (expiry_day record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (root_symbol record) ++
      encode_bytes 1 (symbol_month record) ++
      encode_bytes 2 (symbol_year record) ++
      encode_bytes 2 (expiry_day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (root_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (symbol_month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (symbol_year_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (expiry_day_value, bytes) =>
                      Some ({| root_symbol := root_symbol_value; symbol_month := symbol_month_value; symbol_year := symbol_year_value; expiry_day := expiry_day_value |}, bytes)
                  end
              end
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

  End FutureProduct.

  Module FuturesRequestForQuoteRfqMessage.

    (** Futures Request for Quote (RFQ) message *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
      future_product : FutureProduct.t;
      requested_size : list byte;
      requested_market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      FutureProduct.bounded (future_product record) /\
      Datatypes.length (requested_size record) = 8 /\
      Datatypes.length (requested_market_side record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      FutureProduct.encode (future_product record) ++
      encode_bytes 8 (requested_size record) ++
      encode_bytes 1 (requested_market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              match FutureProduct.decode bytes with
              | None => None
              | Some (future_product_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (requested_size_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (requested_market_side_value, bytes) =>
                          Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value; future_product := future_product_value; requested_size := requested_size_value; requested_market_side := requested_market_side_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length, !FutureProduct.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite FutureProduct.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec | apply FutureProduct.eq_dec]. Defined.

  End FuturesRequestForQuoteRfqMessage.

  Module StrategyRequestForQuoteRfqMessage.

    (** Strategy Request for Quote (RFQ) message *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
      symbol : list byte;
      requested_size : list byte;
      requested_market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (requested_size record) = 8 /\
      Datatypes.length (requested_market_side record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 8 (requested_size record) ++
      encode_bytes 1 (requested_market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
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
                          Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value; symbol := symbol_value; requested_size := requested_size_value; requested_market_side := requested_market_side_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End StrategyRequestForQuoteRfqMessage.

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
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
      future_product : FutureProduct.t;
      series_status : list byte;
      scheduled_status_change_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      FutureProduct.bounded (future_product record) /\
      Datatypes.length (series_status record) = 1 /\
      Datatypes.length (scheduled_status_change_time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      FutureProduct.encode (future_product record) ++
      encode_bytes 1 (series_status record) ++
      encode_bytes 6 (scheduled_status_change_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              match FutureProduct.decode bytes with
              | None => None
              | Some (future_product_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (series_status_value, bytes) =>
                      match decode_bytes 6 bytes with
                      | None => None
                      | Some (scheduled_status_change_time_value, bytes) =>
                          Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value; future_product := future_product_value; series_status := series_status_value; scheduled_status_change_time := scheduled_status_change_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length, !FutureProduct.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite FutureProduct.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec | apply FutureProduct.eq_dec]. Defined.

  End InstrumentScheduleNoticeFutureMessage.

  Module InstrumentScheduleNoticeStrategyMessage.

    (** Instrument Schedule Notice Strategy message *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
      strategy_symbol : list byte;
      series_status : list byte;
      scheduled_status_change_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (strategy_symbol record) = 30 /\
      Datatypes.length (series_status record) = 1 /\
      Datatypes.length (scheduled_status_change_time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (strategy_symbol record) ++
      encode_bytes 1 (series_status record) ++
      encode_bytes 6 (scheduled_status_change_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
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
                          Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value; strategy_symbol := strategy_symbol_value; series_status := series_status_value; scheduled_status_change_time := scheduled_status_change_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End InstrumentScheduleNoticeStrategyMessage.

  Module BidPriceQuoteOpeningPair.

    Record t := {
      bid_price_quote_opening : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_opening record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (bid_price_quote_opening record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (bid_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_opening := bid_price_quote_opening_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteOpeningPair.

  Module BidPriceQuoteNumericNegativeWholePair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericNegativeWholePair.

  Module BidPriceQuoteNumericNegativeTenPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericNegativeTenPair.

  Module BidPriceQuoteNumericNegativeHundredPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericNegativeHundredPair.

  Module BidPriceQuoteNumericNegativeThousandPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericNegativeThousandPair.

  Module BidPriceQuoteNumericNegativeTenThousandPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericNegativeTenThousandPair.

  Module BidPriceQuoteNumericNegativeHundredThousandPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericNegativeHundredThousandPair.

  Module BidPriceQuoteNumericNegativeMillionPair.

    Record t := {
      raw_bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_quote_numeric record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_quote_numeric := raw_bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericNegativeMillionPair.

  Module BidPriceQuoteNumericPair.

    Record t := {
      bid_price_quote_numeric : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_quote_numeric record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (bid_price_quote_numeric record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (bid_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_quote_numeric := bid_price_quote_numeric_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceQuoteNumericPair.

  Module AskPriceQuoteOpeningPair.

    Record t := {
      ask_price_quote_opening : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_opening record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (ask_price_quote_opening record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (ask_price_quote_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_opening := ask_price_quote_opening_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteOpeningPair.

  Module AskPriceQuoteNumericNegativeWholePair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericNegativeWholePair.

  Module AskPriceQuoteNumericNegativeTenPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericNegativeTenPair.

  Module AskPriceQuoteNumericNegativeHundredPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericNegativeHundredPair.

  Module AskPriceQuoteNumericNegativeThousandPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericNegativeThousandPair.

  Module AskPriceQuoteNumericNegativeTenThousandPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericNegativeTenThousandPair.

  Module AskPriceQuoteNumericNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericNegativeHundredThousandPair.

  Module AskPriceQuoteNumericNegativeMillionPair.

    Record t := {
      raw_ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_quote_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_quote_numeric := raw_ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericNegativeMillionPair.

  Module AskPriceQuoteNumericPair.

    Record t := {
      ask_price_quote_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_quote_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (ask_price_quote_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (ask_price_quote_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_quote_numeric := ask_price_quote_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceQuoteNumericPair.

  Module AskPriceFuturesDepthMarketDepthLevelHFOpeningPair.

    Record t := {
      ask_price_futures_depth_opening : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_futures_depth_opening record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (ask_price_futures_depth_opening record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (ask_price_futures_depth_opening_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_futures_depth_opening := ask_price_futures_depth_opening_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthMarketDepthLevelHFOpeningPair.

  Module AskPriceFuturesDepthNumericNegativeWholePair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthNumericNegativeWholePair.

  Module AskPriceFuturesDepthNumericNegativeTenPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthNumericNegativeTenPair.

  Module AskPriceFuturesDepthNumericNegativeHundredPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthNumericNegativeHundredPair.

  Module AskPriceFuturesDepthNumericNegativeThousandPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthNumericNegativeThousandPair.

  Module AskPriceFuturesDepthNumericNegativeTenThousandPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthNumericNegativeTenThousandPair.

  Module AskPriceFuturesDepthNumericNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthNumericNegativeHundredThousandPair.

  Module AskPriceFuturesDepthNumericNegativeMillionPair.

    Record t := {
      raw_ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_futures_depth_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_futures_depth_numeric := raw_ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthNumericNegativeMillionPair.

  Module AskPriceFuturesDepthMarketDepthLevelHFNumericPair.

    Record t := {
      ask_price_futures_depth_numeric : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_futures_depth_numeric record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (ask_price_futures_depth_numeric record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (ask_price_futures_depth_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_futures_depth_numeric := ask_price_futures_depth_numeric_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceFuturesDepthMarketDepthLevelHFNumericPair.

  Module PriceNegativeWholePair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 7 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
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

  End PriceNegativeWholePair.

  Module PriceNegativeTenPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 7 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
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

  End PriceNegativeTenPair.

  Module PriceNegativeHundredPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 7 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
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

  End PriceNegativeHundredPair.

  Module PriceNegativeThousandPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 7 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
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

  End PriceNegativeThousandPair.

  Module PriceNegativeTenThousandPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 7 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
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

  End PriceNegativeTenThousandPair.

  Module PriceNegativeHundredThousandPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 7 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
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

  End PriceNegativeHundredThousandPair.

  Module PriceNegativeMillionPair.

    Record t := {
      raw_price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_price record) = 7 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| raw_price := raw_price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
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

  End PriceNegativeMillionPair.

  Module PriceNumericPair.

    Record t := {
      price : list byte;
      price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (price record) = 7 /\
      Datatypes.length (price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (price record) ++
      encode_bytes 1 (price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_fraction_indicator_value, bytes) =>
              Some ({| price := price_value; price_fraction_indicator := price_fraction_indicator_value |}, bytes)
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

  End PriceNumericPair.

  Module MaximumThresholdPriceNegativeWholePair.

    Record t := {
      raw_maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price := raw_maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceNegativeWholePair.

  Module MaximumThresholdPriceNegativeTenPair.

    Record t := {
      raw_maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price := raw_maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceNegativeTenPair.

  Module MaximumThresholdPriceNegativeHundredPair.

    Record t := {
      raw_maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price := raw_maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceNegativeHundredPair.

  Module MaximumThresholdPriceNegativeThousandPair.

    Record t := {
      raw_maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price := raw_maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceNegativeThousandPair.

  Module MaximumThresholdPriceNegativeTenThousandPair.

    Record t := {
      raw_maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price := raw_maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceNegativeTenThousandPair.

  Module MaximumThresholdPriceNegativeHundredThousandPair.

    Record t := {
      raw_maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price := raw_maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceNegativeHundredThousandPair.

  Module MaximumThresholdPriceNegativeMillionPair.

    Record t := {
      raw_maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price := raw_maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceNegativeMillionPair.

  Module MaximumThresholdPriceNumericPair.

    Record t := {
      maximum_threshold_price : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (maximum_threshold_price record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (maximum_threshold_price record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (maximum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| maximum_threshold_price := maximum_threshold_price_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceNumericPair.

  Module MinimumThresholdPriceNegativeWholePair.

    Record t := {
      raw_minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price := raw_minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceNegativeWholePair.

  Module MinimumThresholdPriceNegativeTenPair.

    Record t := {
      raw_minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price := raw_minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceNegativeTenPair.

  Module MinimumThresholdPriceNegativeHundredPair.

    Record t := {
      raw_minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price := raw_minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceNegativeHundredPair.

  Module MinimumThresholdPriceNegativeThousandPair.

    Record t := {
      raw_minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price := raw_minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceNegativeThousandPair.

  Module MinimumThresholdPriceNegativeTenThousandPair.

    Record t := {
      raw_minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price := raw_minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceNegativeTenThousandPair.

  Module MinimumThresholdPriceNegativeHundredThousandPair.

    Record t := {
      raw_minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price := raw_minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceNegativeHundredThousandPair.

  Module MinimumThresholdPriceNegativeMillionPair.

    Record t := {
      raw_minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price := raw_minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceNegativeMillionPair.

  Module MinimumThresholdPriceNumericPair.

    Record t := {
      minimum_threshold_price : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (minimum_threshold_price record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (minimum_threshold_price record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (minimum_threshold_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| minimum_threshold_price := minimum_threshold_price_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceNumericPair.

  Module TickIncrementNumericPair.

    Record t := {
      tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_increment_numeric record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| tick_increment_numeric := tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericPair.

  Module TickIncrementNumericNegativeWholePair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericNegativeWholePair.

  Module TickIncrementNumericNegativeTenPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericNegativeTenPair.

  Module TickIncrementNumericNegativeHundredPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericNegativeHundredPair.

  Module TickIncrementNumericNegativeThousandPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericNegativeThousandPair.

  Module TickIncrementNumericNegativeTenThousandPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericNegativeTenThousandPair.

  Module TickIncrementNumericNegativeHundredThousandPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericNegativeHundredThousandPair.

  Module TickIncrementNumericNegativeMillionPair.

    Record t := {
      raw_tick_increment_numeric : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_increment_numeric record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_increment_numeric record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_increment_numeric_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_increment_numeric := raw_tick_increment_numeric_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementNumericNegativeMillionPair.

  Module TickIncrementRawPair.

    Record t := {
      tick_increment_raw : list byte;
      tick_increment_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_increment_raw record) = 7 /\
      Datatypes.length (tick_increment_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (tick_increment_raw record) ++
      encode_bytes 1 (tick_increment_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (tick_increment_raw_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_increment_fraction_indicator_value, bytes) =>
              Some ({| tick_increment_raw := tick_increment_raw_value; tick_increment_fraction_indicator := tick_increment_fraction_indicator_value |}, bytes)
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

  End TickIncrementRawPair.

  Module TickValueNegativeWholePair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 7 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
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

  End TickValueNegativeWholePair.

  Module TickValueNegativeTenPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 7 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
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

  End TickValueNegativeTenPair.

  Module TickValueNegativeHundredPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 7 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
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

  End TickValueNegativeHundredPair.

  Module TickValueNegativeThousandPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 7 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
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

  End TickValueNegativeThousandPair.

  Module TickValueNegativeTenThousandPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 7 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
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

  End TickValueNegativeTenThousandPair.

  Module TickValueNegativeHundredThousandPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 7 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
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

  End TickValueNegativeHundredThousandPair.

  Module TickValueNegativeMillionPair.

    Record t := {
      raw_tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_value record) = 7 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_value := raw_tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
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

  End TickValueNegativeMillionPair.

  Module TickValueNumericPair.

    Record t := {
      tick_value : list byte;
      tick_value_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_value record) = 7 /\
      Datatypes.length (tick_value_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (tick_value record) ++
      encode_bytes 1 (tick_value_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (tick_value_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_value_fraction_indicator_value, bytes) =>
              Some ({| tick_value := tick_value_value; tick_value_fraction_indicator := tick_value_fraction_indicator_value |}, bytes)
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

  End TickValueNumericPair.

  Module UnderlyingInstrumentKeysMessage.

    (** The 'Underlying Instrument Keys' message will be the first messages sent during the day. There is no 'Underlying Summary' message attached to the 'Instrument Keys' messages *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
      group_instrument : list byte;
      instrument : list byte;
      instrument_external_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (group_instrument record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (instrument_external_code record) = 30.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 2 (group_instrument record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 30 (instrument_external_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
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
                          Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value; group_instrument := group_instrument_value; instrument := instrument_value; instrument_external_code := instrument_external_code_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End UnderlyingInstrumentKeysMessage.

  Module MaximumThresholdPriceFuturesNegativeWholePair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceFuturesNegativeWholePair.

  Module MaximumThresholdPriceFuturesNegativeTenPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceFuturesNegativeTenPair.

  Module MaximumThresholdPriceFuturesNegativeHundredPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceFuturesNegativeHundredPair.

  Module MaximumThresholdPriceFuturesNegativeThousandPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceFuturesNegativeThousandPair.

  Module MaximumThresholdPriceFuturesNegativeTenThousandPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceFuturesNegativeTenThousandPair.

  Module MaximumThresholdPriceFuturesNegativeHundredThousandPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceFuturesNegativeHundredThousandPair.

  Module MaximumThresholdPriceFuturesNegativeMillionPair.

    Record t := {
      raw_maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_maximum_threshold_price_futures record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_maximum_threshold_price_futures := raw_maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceFuturesNegativeMillionPair.

  Module MaximumThresholdPriceFuturesNumericPair.

    Record t := {
      maximum_threshold_price_futures : list byte;
      maximum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (maximum_threshold_price_futures record) = 7 /\
      Datatypes.length (maximum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (maximum_threshold_price_futures record) ++
      encode_bytes 1 (maximum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (maximum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (maximum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| maximum_threshold_price_futures := maximum_threshold_price_futures_value; maximum_threshold_price_fraction_indicator := maximum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MaximumThresholdPriceFuturesNumericPair.

  Module MinimumThresholdPriceFuturesNegativeWholePair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceFuturesNegativeWholePair.

  Module MinimumThresholdPriceFuturesNegativeTenPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceFuturesNegativeTenPair.

  Module MinimumThresholdPriceFuturesNegativeHundredPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceFuturesNegativeHundredPair.

  Module MinimumThresholdPriceFuturesNegativeThousandPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceFuturesNegativeThousandPair.

  Module MinimumThresholdPriceFuturesNegativeTenThousandPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceFuturesNegativeTenThousandPair.

  Module MinimumThresholdPriceFuturesNegativeHundredThousandPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceFuturesNegativeHundredThousandPair.

  Module MinimumThresholdPriceFuturesNegativeMillionPair.

    Record t := {
      raw_minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_minimum_threshold_price_futures record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| raw_minimum_threshold_price_futures := raw_minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceFuturesNegativeMillionPair.

  Module MinimumThresholdPriceFuturesNumericPair.

    Record t := {
      minimum_threshold_price_futures : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (minimum_threshold_price_futures record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (minimum_threshold_price_futures record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (minimum_threshold_price_futures_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| minimum_threshold_price_futures := minimum_threshold_price_futures_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
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

  End MinimumThresholdPriceFuturesNumericPair.

  Module AssociatedProduct.

    (** Associated future product symbology *)
    Record t := {
      root_symbol : list byte;
      symbol_month : list byte;
      symbol_year : list byte;
      expiry_day : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (root_symbol record) = 6 /\
      Datatypes.length (symbol_month record) = 1 /\
      Datatypes.length (symbol_year record) = 2 /\
      Datatypes.length (expiry_day record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (root_symbol record) ++
      encode_bytes 1 (symbol_month record) ++
      encode_bytes 2 (symbol_year record) ++
      encode_bytes 2 (expiry_day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (root_symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (symbol_month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (symbol_year_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (expiry_day_value, bytes) =>
                      Some ({| root_symbol := root_symbol_value; symbol_month := symbol_month_value; symbol_year := symbol_year_value; expiry_day := expiry_day_value |}, bytes)
                  end
              end
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

  End AssociatedProduct.

  Module BidPriceSummaryNegativeWholePair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceSummaryNegativeWholePair.

  Module BidPriceSummaryNegativeTenPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceSummaryNegativeTenPair.

  Module BidPriceSummaryNegativeHundredPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceSummaryNegativeHundredPair.

  Module BidPriceSummaryNegativeThousandPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceSummaryNegativeThousandPair.

  Module BidPriceSummaryNegativeTenThousandPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceSummaryNegativeTenThousandPair.

  Module BidPriceSummaryNegativeHundredThousandPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceSummaryNegativeHundredThousandPair.

  Module BidPriceSummaryNegativeMillionPair.

    Record t := {
      raw_bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_bid_price_summary record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| raw_bid_price_summary := raw_bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceSummaryNegativeMillionPair.

  Module BidPriceSummaryNumericPair.

    Record t := {
      bid_price_summary : list byte;
      bid_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (bid_price_summary record) = 7 /\
      Datatypes.length (bid_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (bid_price_summary record) ++
      encode_bytes 1 (bid_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (bid_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (bid_price_fraction_indicator_value, bytes) =>
              Some ({| bid_price_summary := bid_price_summary_value; bid_price_fraction_indicator := bid_price_fraction_indicator_value |}, bytes)
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

  End BidPriceSummaryNumericPair.

  Module AskPriceSummaryNegativeWholePair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceSummaryNegativeWholePair.

  Module AskPriceSummaryNegativeTenPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceSummaryNegativeTenPair.

  Module AskPriceSummaryNegativeHundredPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceSummaryNegativeHundredPair.

  Module AskPriceSummaryNegativeThousandPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceSummaryNegativeThousandPair.

  Module AskPriceSummaryNegativeTenThousandPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceSummaryNegativeTenThousandPair.

  Module AskPriceSummaryNegativeHundredThousandPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceSummaryNegativeHundredThousandPair.

  Module AskPriceSummaryNegativeMillionPair.

    Record t := {
      raw_ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_ask_price_summary record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| raw_ask_price_summary := raw_ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceSummaryNegativeMillionPair.

  Module AskPriceSummaryNumericPair.

    Record t := {
      ask_price_summary : list byte;
      ask_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (ask_price_summary record) = 7 /\
      Datatypes.length (ask_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (ask_price_summary record) ++
      encode_bytes 1 (ask_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (ask_price_summary_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (ask_price_fraction_indicator_value, bytes) =>
              Some ({| ask_price_summary := ask_price_summary_value; ask_price_fraction_indicator := ask_price_fraction_indicator_value |}, bytes)
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

  End AskPriceSummaryNumericPair.

  Module LastPriceNegativeWholePair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 7 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeWholePair.

  Module LastPriceNegativeTenPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 7 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeTenPair.

  Module LastPriceNegativeHundredPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 7 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeHundredPair.

  Module LastPriceNegativeThousandPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 7 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeThousandPair.

  Module LastPriceNegativeTenThousandPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 7 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeTenThousandPair.

  Module LastPriceNegativeHundredThousandPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 7 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeHundredThousandPair.

  Module LastPriceNegativeMillionPair.

    Record t := {
      raw_last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_last_price record) = 7 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| raw_last_price := raw_last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNegativeMillionPair.

  Module LastPriceNumericPair.

    Record t := {
      last_price : list byte;
      last_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (last_price record) = 7 /\
      Datatypes.length (last_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (last_price record) ++
      encode_bytes 1 (last_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (last_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (last_price_fraction_indicator_value, bytes) =>
              Some ({| last_price := last_price_value; last_price_fraction_indicator := last_price_fraction_indicator_value |}, bytes)
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

  End LastPriceNumericPair.

  Module OpenPriceNegativeWholePair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 7 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeWholePair.

  Module OpenPriceNegativeTenPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 7 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeTenPair.

  Module OpenPriceNegativeHundredPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 7 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeHundredPair.

  Module OpenPriceNegativeThousandPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 7 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeThousandPair.

  Module OpenPriceNegativeTenThousandPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 7 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeTenThousandPair.

  Module OpenPriceNegativeHundredThousandPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 7 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeHundredThousandPair.

  Module OpenPriceNegativeMillionPair.

    Record t := {
      raw_open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_open_price record) = 7 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| raw_open_price := raw_open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNegativeMillionPair.

  Module OpenPriceNumericPair.

    Record t := {
      open_price : list byte;
      open_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (open_price record) = 7 /\
      Datatypes.length (open_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (open_price record) ++
      encode_bytes 1 (open_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (open_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (open_price_fraction_indicator_value, bytes) =>
              Some ({| open_price := open_price_value; open_price_fraction_indicator := open_price_fraction_indicator_value |}, bytes)
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

  End OpenPriceNumericPair.

  Module HighPriceNegativeWholePair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 7 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeWholePair.

  Module HighPriceNegativeTenPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 7 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeTenPair.

  Module HighPriceNegativeHundredPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 7 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeHundredPair.

  Module HighPriceNegativeThousandPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 7 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeThousandPair.

  Module HighPriceNegativeTenThousandPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 7 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeTenThousandPair.

  Module HighPriceNegativeHundredThousandPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 7 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeHundredThousandPair.

  Module HighPriceNegativeMillionPair.

    Record t := {
      raw_high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_high_price record) = 7 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| raw_high_price := raw_high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNegativeMillionPair.

  Module HighPriceNumericPair.

    Record t := {
      high_price : list byte;
      high_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (high_price record) = 7 /\
      Datatypes.length (high_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (high_price record) ++
      encode_bytes 1 (high_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (high_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (high_price_fraction_indicator_value, bytes) =>
              Some ({| high_price := high_price_value; high_price_fraction_indicator := high_price_fraction_indicator_value |}, bytes)
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

  End HighPriceNumericPair.

  Module LowPriceNegativeWholePair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 7 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeWholePair.

  Module LowPriceNegativeTenPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 7 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeTenPair.

  Module LowPriceNegativeHundredPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 7 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeHundredPair.

  Module LowPriceNegativeThousandPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 7 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeThousandPair.

  Module LowPriceNegativeTenThousandPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 7 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeTenThousandPair.

  Module LowPriceNegativeHundredThousandPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 7 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeHundredThousandPair.

  Module LowPriceNegativeMillionPair.

    Record t := {
      raw_low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_low_price record) = 7 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| raw_low_price := raw_low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNegativeMillionPair.

  Module LowPriceNumericPair.

    Record t := {
      low_price : list byte;
      low_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (low_price record) = 7 /\
      Datatypes.length (low_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (low_price record) ++
      encode_bytes 1 (low_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (low_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (low_price_fraction_indicator_value, bytes) =>
              Some ({| low_price := low_price_value; low_price_fraction_indicator := low_price_fraction_indicator_value |}, bytes)
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

  End LowPriceNumericPair.

  Module SettlementPriceNegativeWholePair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceNegativeWholePair.

  Module SettlementPriceNegativeTenPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceNegativeTenPair.

  Module SettlementPriceNegativeHundredPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceNegativeHundredPair.

  Module SettlementPriceNegativeThousandPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceNegativeThousandPair.

  Module SettlementPriceNegativeTenThousandPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceNegativeTenThousandPair.

  Module SettlementPriceNegativeHundredThousandPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceNegativeHundredThousandPair.

  Module SettlementPriceNegativeMillionPair.

    Record t := {
      raw_settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price := raw_settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceNegativeMillionPair.

  Module SettlementPriceNumericPair.

    Record t := {
      settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| settlement_price := settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceNumericPair.

  Module PreviousSettlementPriceNegativeWholePair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 7 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementPriceNegativeWholePair.

  Module PreviousSettlementPriceNegativeTenPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 7 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementPriceNegativeTenPair.

  Module PreviousSettlementPriceNegativeHundredPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 7 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementPriceNegativeHundredPair.

  Module PreviousSettlementPriceNegativeThousandPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 7 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementPriceNegativeThousandPair.

  Module PreviousSettlementPriceNegativeTenThousandPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 7 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementPriceNegativeTenThousandPair.

  Module PreviousSettlementPriceNegativeHundredThousandPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 7 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementPriceNegativeHundredThousandPair.

  Module PreviousSettlementPriceNegativeMillionPair.

    Record t := {
      raw_previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement_price record) = 7 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement_price := raw_previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementPriceNegativeMillionPair.

  Module PreviousSettlementPriceNumericPair.

    Record t := {
      previous_settlement_price : list byte;
      previous_settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (previous_settlement_price record) = 7 /\
      Datatypes.length (previous_settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (previous_settlement_price record) ++
      encode_bytes 1 (previous_settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (previous_settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_price_fraction_indicator_value, bytes) =>
              Some ({| previous_settlement_price := previous_settlement_price_value; previous_settlement_price_fraction_indicator := previous_settlement_price_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementPriceNumericPair.

  Module OpeningPriceNegativeWholePair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 7 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
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

  End OpeningPriceNegativeWholePair.

  Module OpeningPriceNegativeTenPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 7 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
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

  End OpeningPriceNegativeTenPair.

  Module OpeningPriceNegativeHundredPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 7 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
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

  End OpeningPriceNegativeHundredPair.

  Module OpeningPriceNegativeThousandPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 7 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
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

  End OpeningPriceNegativeThousandPair.

  Module OpeningPriceNegativeTenThousandPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 7 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
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

  End OpeningPriceNegativeTenThousandPair.

  Module OpeningPriceNegativeHundredThousandPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 7 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
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

  End OpeningPriceNegativeHundredThousandPair.

  Module OpeningPriceNegativeMillionPair.

    Record t := {
      raw_opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_opening_price record) = 7 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| raw_opening_price := raw_opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
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

  End OpeningPriceNegativeMillionPair.

  Module OpeningPriceNumericPair.

    Record t := {
      opening_price : list byte;
      opening_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (opening_price record) = 7 /\
      Datatypes.length (opening_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (opening_price record) ++
      encode_bytes 1 (opening_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (opening_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (opening_price_fraction_indicator_value, bytes) =>
              Some ({| opening_price := opening_price_value; opening_price_fraction_indicator := opening_price_fraction_indicator_value |}, bytes)
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

  End OpeningPriceNumericPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeWholePair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceFutureOptionsSummaryMessageNegativeWholePair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeTenPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceFutureOptionsSummaryMessageNegativeTenPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeHundredPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceFutureOptionsSummaryMessageNegativeHundredPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeThousandPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceFutureOptionsSummaryMessageNegativeThousandPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeTenThousandPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceFutureOptionsSummaryMessageNegativeTenThousandPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeHundredThousandPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceFutureOptionsSummaryMessageNegativeHundredThousandPair.

  Module SettlementPriceFutureOptionsSummaryMessageNegativeMillionPair.

    Record t := {
      raw_settlement_price_future_options_summary_message : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_settlement_price_future_options_summary_message record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_settlement_price_future_options_summary_message record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_settlement_price_future_options_summary_message_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| raw_settlement_price_future_options_summary_message := raw_settlement_price_future_options_summary_message_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceFutureOptionsSummaryMessageNegativeMillionPair.

  Module SettlementPriceFutureOptionsSummaryMessageNumericPair.

    Record t := {
      settlement_price : list byte;
      settlement_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (settlement_price record) = 7 /\
      Datatypes.length (settlement_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (settlement_price record) ++
      encode_bytes 1 (settlement_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (settlement_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (settlement_price_fraction_indicator_value, bytes) =>
              Some ({| settlement_price := settlement_price_value; settlement_price_fraction_indicator := settlement_price_fraction_indicator_value |}, bytes)
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

  End SettlementPriceFutureOptionsSummaryMessageNumericPair.

  Module PreviousSettlementNegativeWholePair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 7 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementNegativeWholePair.

  Module PreviousSettlementNegativeTenPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 7 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementNegativeTenPair.

  Module PreviousSettlementNegativeHundredPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 7 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementNegativeHundredPair.

  Module PreviousSettlementNegativeThousandPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 7 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementNegativeThousandPair.

  Module PreviousSettlementNegativeTenThousandPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 7 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementNegativeTenThousandPair.

  Module PreviousSettlementNegativeHundredThousandPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 7 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementNegativeHundredThousandPair.

  Module PreviousSettlementNegativeMillionPair.

    Record t := {
      raw_previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_previous_settlement record) = 7 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| raw_previous_settlement := raw_previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementNegativeMillionPair.

  Module PreviousSettlementNumericPair.

    Record t := {
      previous_settlement : list byte;
      previous_settlement_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (previous_settlement record) = 7 /\
      Datatypes.length (previous_settlement_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (previous_settlement record) ++
      encode_bytes 1 (previous_settlement_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (previous_settlement_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_settlement_fraction_indicator_value, bytes) =>
              Some ({| previous_settlement := previous_settlement_value; previous_settlement_fraction_indicator := previous_settlement_fraction_indicator_value |}, bytes)
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

  End PreviousSettlementNumericPair.

  Module ExternalPriceAtSourceNegativeWholePair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 7 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
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

  End ExternalPriceAtSourceNegativeWholePair.

  Module ExternalPriceAtSourceNegativeTenPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 7 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
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

  End ExternalPriceAtSourceNegativeTenPair.

  Module ExternalPriceAtSourceNegativeHundredPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 7 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
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

  End ExternalPriceAtSourceNegativeHundredPair.

  Module ExternalPriceAtSourceNegativeThousandPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 7 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
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

  End ExternalPriceAtSourceNegativeThousandPair.

  Module ExternalPriceAtSourceNegativeTenThousandPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 7 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
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

  End ExternalPriceAtSourceNegativeTenThousandPair.

  Module ExternalPriceAtSourceNegativeHundredThousandPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 7 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
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

  End ExternalPriceAtSourceNegativeHundredThousandPair.

  Module ExternalPriceAtSourceNegativeMillionPair.

    Record t := {
      raw_external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_external_price_at_source record) = 7 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| raw_external_price_at_source := raw_external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
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

  End ExternalPriceAtSourceNegativeMillionPair.

  Module ExternalPriceAtSourceNumericPair.

    Record t := {
      external_price_at_source : list byte;
      external_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (external_price_at_source record) = 7 /\
      Datatypes.length (external_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (external_price_at_source record) ++
      encode_bytes 1 (external_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (external_price_at_source_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (external_price_fraction_indicator_value, bytes) =>
              Some ({| external_price_at_source := external_price_at_source_value; external_price_fraction_indicator := external_price_fraction_indicator_value |}, bytes)
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

  End ExternalPriceAtSourceNumericPair.

  Module BeginningOfOptionsSummaryMessage.

    (** This message indicates that the beginning and the end of day N: Option Summary messages are to follow. Other messages (such as bulletins) can be interspersed with the summaries. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End BeginningOfOptionsSummaryMessage.

  Module BeginningOfFutureOptionsSummaryMessage.

    (** This message indicates that the beginning and the end of day NB: Future Options Summary messages are to follow. Other messages (such as bulletins) can be interspersed with the summaries. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End BeginningOfFutureOptionsSummaryMessage.

  Module BeginningOfFuturesSummaryMessage.

    (** This message indicates that the beginning or end-of-day NF: Future Summary messages are to follow. Other messages can be interspersed with the summaries. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End BeginningOfFuturesSummaryMessage.

  Module BeginningOfStrategySummaryMessage.

    (** This message indicates that the beginning or the end of day NS: Strategy Summary messages are to follow. Other messages can be interspersed with the summaries. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End BeginningOfStrategySummaryMessage.

  Module GroupStatusMessage.

    (** This message will be sent when a group of trading instruments enters a new status. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
      root_symbol_group : list byte;
      group_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (root_symbol_group record) = 6 /\
      Datatypes.length (group_status record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (root_symbol_group record) ++
      encode_bytes 1 (group_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (root_symbol_group_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (group_status_value, bytes) =>
                      Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value; root_symbol_group := root_symbol_group_value; group_status := group_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End GroupStatusMessage.

  Module GroupStatusStrategiesMessage.

    (** This message will be sent when a strategy group of trading instruments enters a new status. All strategies have a predetermined group that can be found in the JS: Strategy Instrument Keys message. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
      group_instrument : list byte;
      group_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (group_instrument record) = 2 /\
      Datatypes.length (group_status record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 2 (group_instrument record) ++
      encode_bytes 1 (group_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (group_instrument_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (group_status_value, bytes) =>
                      Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value; group_instrument := group_instrument_value; group_status := group_status_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End GroupStatusStrategiesMessage.

  Module RegularTextBulletin.

    (** Bulletin Type 1, which the Bulletin Type field selects. *)
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

    (** This bulletin type will be used for bulletins relating to a specific trading instrument. *)
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

    (** The S: End of Sales message is sent when there is no more trading activity to be transmitted. This occurs after the closing of the market. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      reserved : list byte;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (reserved record) = 1 /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (reserved record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reserved_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_value, bytes) =>
                  Some ({| long_message_header := long_message_header_value; reserved := reserved_value; time := time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End EndOfSalesMessage.

  Module MinPriceNegativeWholePair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 7 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
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

  End MinPriceNegativeWholePair.

  Module MinPriceNegativeTenPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 7 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
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

  End MinPriceNegativeTenPair.

  Module MinPriceNegativeHundredPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 7 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
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

  End MinPriceNegativeHundredPair.

  Module MinPriceNegativeThousandPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 7 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
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

  End MinPriceNegativeThousandPair.

  Module MinPriceNegativeTenThousandPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 7 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
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

  End MinPriceNegativeTenThousandPair.

  Module MinPriceNegativeHundredThousandPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 7 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
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

  End MinPriceNegativeHundredThousandPair.

  Module MinPriceNegativeMillionPair.

    Record t := {
      raw_min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_min_price record) = 7 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| raw_min_price := raw_min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
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

  End MinPriceNegativeMillionPair.

  Module MinPriceNumericPair.

    Record t := {
      min_price : list byte;
      min_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (min_price record) = 7 /\
      Datatypes.length (min_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (min_price record) ++
      encode_bytes 1 (min_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (min_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (min_price_fraction_indicator_value, bytes) =>
              Some ({| min_price := min_price_value; min_price_fraction_indicator := min_price_fraction_indicator_value |}, bytes)
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

  End MinPriceNumericPair.

  Module TickPriceNegativeWholePair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 7 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
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

  End TickPriceNegativeWholePair.

  Module TickPriceNegativeTenPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 7 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
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

  End TickPriceNegativeTenPair.

  Module TickPriceNegativeHundredPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 7 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
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

  End TickPriceNegativeHundredPair.

  Module TickPriceNegativeThousandPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 7 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
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

  End TickPriceNegativeThousandPair.

  Module TickPriceNegativeTenThousandPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 7 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
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

  End TickPriceNegativeTenThousandPair.

  Module TickPriceNegativeHundredThousandPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 7 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
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

  End TickPriceNegativeHundredThousandPair.

  Module TickPriceNegativeMillionPair.

    Record t := {
      raw_tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (raw_tick_price record) = 7 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (raw_tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (raw_tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| raw_tick_price := raw_tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
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

  End TickPriceNegativeMillionPair.

  Module TickPriceNumericPair.

    Record t := {
      tick_price : list byte;
      tick_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (tick_price record) = 7 /\
      Datatypes.length (tick_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (tick_price record) ++
      encode_bytes 1 (tick_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (tick_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (tick_price_fraction_indicator_value, bytes) =>
              Some ({| tick_price := tick_price_value; tick_price_fraction_indicator := tick_price_fraction_indicator_value |}, bytes)
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

  End TickPriceNumericPair.

  Module EndOfTransmissionMessage.

    (** This message will be sent daily to indicate that the day’s transmission is complete. No HSVF messages will be transmitted afterwards. Transmission will resume the following day. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      exchange_id : list byte;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (time_value, bytes) =>
                  Some ({| long_message_header := long_message_header_value; exchange_id := exchange_id_value; time := time_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End EndOfTransmissionMessage.

  Module CircuitAssuranceMessage.

    (** This message is sent out if no messages are sent by SAM for more than one minute after the broadcast has started (i.e., at the termination of the Test Loop message). This will be an assurance that the line is up. This message will continue to be sent until the U: End of Transmission message is sent. The Circuit Assurance message will repeat the sequence number of the previous record transmitted (except if it is a re-transmit message), i.e. it will not increase the sequence number. *)
    Record t := {
      long_message_header : LongMessageHeader.t;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader.bounded (long_message_header record) /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader.encode (long_message_header record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (time_value, bytes) =>
              Some ({| long_message_header := long_message_header_value; time := time_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !LongMessageHeader.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader.eq_dec]. Defined.

  End CircuitAssuranceMessage.

End MxSolaMulticastV1122.
