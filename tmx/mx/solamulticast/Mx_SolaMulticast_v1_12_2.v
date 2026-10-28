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
      - a Composite rule
      - a run counted by a field
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

  Module LongMessageHeader2.

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

  End LongMessageHeader2.

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

  Module TradePriceNumericPair2.

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

  End TradePriceNumericPair2.

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

  Module LongMessageHeader3.

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

  End LongMessageHeader3.

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

  Module TradePriceNumericPair3.

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

  End TradePriceNumericPair3.

  Module NetChangeNumericPair2.

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

  End NetChangeNumericPair2.

  Module LongMessageHeader4.

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

  End LongMessageHeader4.

  Module TradePriceNumericPair4.

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

  End TradePriceNumericPair4.

  Module NetChangeNumericPair3.

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

  End NetChangeNumericPair3.

  Module LongMessageHeader5.

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

  End LongMessageHeader5.

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

  Module LongMessageHeader6.

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

  End LongMessageHeader6.

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

  Module LongMessageHeader7.

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

  End LongMessageHeader7.

  Module FutureProduct2.

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

  End FutureProduct2.

  Module FuturesRequestForQuoteRfqMessage.

    (** Futures Request for Quote (RFQ) message *)
    Record t := {
      long_message_header : LongMessageHeader7.t;
      exchange_id : list byte;
      future_product : FutureProduct2.t;
      requested_size : list byte;
      requested_market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader7.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      FutureProduct2.bounded (future_product record) /\
      Datatypes.length (requested_size record) = 8 /\
      Datatypes.length (requested_market_side record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader7.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      FutureProduct2.encode (future_product record) ++
      encode_bytes 8 (requested_size record) ++
      encode_bytes 1 (requested_market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader7.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              match FutureProduct2.decode bytes with
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
      rewrite !length_app, !LongMessageHeader7.encode_length, !encode_bytes_length, !FutureProduct2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader7.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite FutureProduct2.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader7.eq_dec | apply FutureProduct2.eq_dec]. Defined.

  End FuturesRequestForQuoteRfqMessage.

  Module LongMessageHeader8.

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

  End LongMessageHeader8.

  Module StrategyRequestForQuoteRfqMessage.

    (** Strategy Request for Quote (RFQ) message *)
    Record t := {
      long_message_header : LongMessageHeader8.t;
      exchange_id : list byte;
      symbol : list byte;
      requested_size : list byte;
      requested_market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader8.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (symbol record) = 30 /\
      Datatypes.length (requested_size record) = 8 /\
      Datatypes.length (requested_market_side record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader8.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (symbol record) ++
      encode_bytes 8 (requested_size record) ++
      encode_bytes 1 (requested_market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader8.decode bytes with
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
      rewrite !length_app, !LongMessageHeader8.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader8.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader8.eq_dec]. Defined.

  End StrategyRequestForQuoteRfqMessage.

  Module LongMessageHeader9.

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

  End LongMessageHeader9.

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

  Module LongMessageHeader10.

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

  End LongMessageHeader10.

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

  Module LongMessageHeader11.

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

  End LongMessageHeader11.

  Module FutureProduct3.

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

  End FutureProduct3.

  Module InstrumentScheduleNoticeFutureMessage.

    (** Instrument Schedule Notice Future message *)
    Record t := {
      long_message_header : LongMessageHeader11.t;
      exchange_id : list byte;
      future_product : FutureProduct3.t;
      series_status : list byte;
      scheduled_status_change_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader11.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      FutureProduct3.bounded (future_product record) /\
      Datatypes.length (series_status record) = 1 /\
      Datatypes.length (scheduled_status_change_time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader11.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      FutureProduct3.encode (future_product record) ++
      encode_bytes 1 (series_status record) ++
      encode_bytes 6 (scheduled_status_change_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader11.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (exchange_id_value, bytes) =>
              match FutureProduct3.decode bytes with
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
      rewrite !length_app, !LongMessageHeader11.encode_length, !encode_bytes_length, !FutureProduct3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader11.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite FutureProduct3.decode_encode by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader11.eq_dec | apply FutureProduct3.eq_dec]. Defined.

  End InstrumentScheduleNoticeFutureMessage.

  Module LongMessageHeader12.

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

  End LongMessageHeader12.

  Module InstrumentScheduleNoticeStrategyMessage.

    (** Instrument Schedule Notice Strategy message *)
    Record t := {
      long_message_header : LongMessageHeader12.t;
      exchange_id : list byte;
      strategy_symbol : list byte;
      series_status : list byte;
      scheduled_status_change_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader12.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (strategy_symbol record) = 30 /\
      Datatypes.length (series_status record) = 1 /\
      Datatypes.length (scheduled_status_change_time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader12.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (strategy_symbol record) ++
      encode_bytes 1 (series_status record) ++
      encode_bytes 6 (scheduled_status_change_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader12.decode bytes with
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
      rewrite !length_app, !LongMessageHeader12.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader12.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader12.eq_dec]. Defined.

  End InstrumentScheduleNoticeStrategyMessage.

  Module LongMessageHeader13.

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

  End LongMessageHeader13.

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

  Module LongMessageHeader14.

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

  End LongMessageHeader14.

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

  Module BidPriceQuoteOpeningPair2.

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

  End BidPriceQuoteOpeningPair2.

  Module BidPriceQuoteNumericPair2.

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

  End BidPriceQuoteNumericPair2.

  Module AskPriceQuoteOpeningPair2.

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

  End AskPriceQuoteOpeningPair2.

  Module AskPriceQuoteNumericPair2.

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

  End AskPriceQuoteNumericPair2.

  Module LongMessageHeader15.

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

  End LongMessageHeader15.

  Module FutureProduct4.

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

  End FutureProduct4.

  Module BidPriceQuoteOpeningPair3.

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

  End BidPriceQuoteOpeningPair3.

  Module BidPriceQuoteNumericPair3.

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

  End BidPriceQuoteNumericPair3.

  Module AskPriceQuoteOpeningPair3.

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

  End AskPriceQuoteOpeningPair3.

  Module AskPriceQuoteNumericPair3.

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

  End AskPriceQuoteNumericPair3.

  Module LongMessageHeader16.

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

  End LongMessageHeader16.

  Module BidPriceQuoteOpeningPair4.

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

  End BidPriceQuoteOpeningPair4.

  Module BidPriceQuoteNumericPair4.

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

  End BidPriceQuoteNumericPair4.

  Module AskPriceQuoteOpeningPair4.

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

  End AskPriceQuoteOpeningPair4.

  Module AskPriceQuoteNumericPair4.

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

  End AskPriceQuoteNumericPair4.

  Module LongMessageHeader17.

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

  End LongMessageHeader17.

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

  Module BidPriceQuoteOpeningPair5.

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

  End BidPriceQuoteOpeningPair5.

  Module BidPriceQuoteNumericPair5.

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

  End BidPriceQuoteNumericPair5.

  Module AskPriceQuoteOpeningPair5.

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

  End AskPriceQuoteOpeningPair5.

  Module AskPriceQuoteNumericPair5.

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

  End AskPriceQuoteNumericPair5.

  Module LongMessageHeader18.

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

  End LongMessageHeader18.

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

  Module BidPriceQuoteOpeningPair6.

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

  End BidPriceQuoteOpeningPair6.

  Module BidPriceQuoteNumericPair6.

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

  End BidPriceQuoteNumericPair6.

  Module AskPriceQuoteOpeningPair6.

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

  End AskPriceQuoteOpeningPair6.

  Module AskPriceQuoteNumericPair6.

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

  End AskPriceQuoteNumericPair6.

  Module LongMessageHeader19.

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

  End LongMessageHeader19.

  Module FutureProduct5.

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

  End FutureProduct5.

  Module BidPriceQuoteOpeningPair7.

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

  End BidPriceQuoteOpeningPair7.

  Module BidPriceQuoteNumericPair7.

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

  End BidPriceQuoteNumericPair7.

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

  Module LongMessageHeader20.

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

  End LongMessageHeader20.

  Module BidPriceQuoteOpeningPair8.

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

  End BidPriceQuoteOpeningPair8.

  Module BidPriceQuoteNumericPair8.

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

  End BidPriceQuoteNumericPair8.

  Module AskPriceQuoteOpeningPair7.

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

  End AskPriceQuoteOpeningPair7.

  Module AskPriceQuoteNumericPair7.

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

  End AskPriceQuoteNumericPair7.

  Module LongMessageHeader21.

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

  End LongMessageHeader21.

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

  Module TradePriceNumericPair5.

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

  End TradePriceNumericPair5.

  Module LongMessageHeader22.

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

  End LongMessageHeader22.

  Module StrikePriceNumericPair11.

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

  End StrikePriceNumericPair11.

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

  Module LongMessageHeader23.

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

  End LongMessageHeader23.

  Module FutureProduct6.

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

  End FutureProduct6.

  Module TradePriceNumericPair6.

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

  End TradePriceNumericPair6.

  Module LongMessageHeader24.

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

  End LongMessageHeader24.

  Module TradePriceNumericPair7.

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

  End TradePriceNumericPair7.

  Module LongMessageHeader25.

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

  End LongMessageHeader25.

  Module StrikePriceNumericPair12.

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

  End StrikePriceNumericPair12.

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

  Module LongMessageHeader26.

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

  End LongMessageHeader26.

  Module StrikePriceNumericPair13.

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

  End StrikePriceNumericPair13.

  Module MaximumThresholdPriceNumericPair2.

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

  End MaximumThresholdPriceNumericPair2.

  Module MinimumThresholdPriceNumericPair2.

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

  End MinimumThresholdPriceNumericPair2.

  Module TickIncrementNumericPair2.

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

  End TickIncrementNumericPair2.

  Module TickIncrementRawPair2.

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

  End TickIncrementRawPair2.

  Module TickValueNumericPair2.

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

  End TickValueNumericPair2.

  Module LongMessageHeader27.

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

  End LongMessageHeader27.

  Module UnderlyingInstrumentKeysMessage.

    (** The 'Underlying Instrument Keys' message will be the first messages sent during the day. There is no 'Underlying Summary' message attached to the 'Instrument Keys' messages *)
    Record t := {
      long_message_header : LongMessageHeader27.t;
      exchange_id : list byte;
      group_instrument : list byte;
      instrument : list byte;
      instrument_external_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader27.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (group_instrument record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (instrument_external_code record) = 30.

    Definition encode (record : t) : list byte :=
      LongMessageHeader27.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 2 (group_instrument record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 30 (instrument_external_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader27.decode bytes with
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
      rewrite !length_app, !LongMessageHeader27.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader27.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader27.eq_dec]. Defined.

  End UnderlyingInstrumentKeysMessage.

  Module LongMessageHeader28.

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

  End LongMessageHeader28.

  Module FutureProduct7.

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

  End FutureProduct7.

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

  Module TickIncrementNumericPair3.

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

  End TickIncrementNumericPair3.

  Module TickIncrementRawPair3.

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

  End TickIncrementRawPair3.

  Module TickValueNumericPair3.

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

  End TickValueNumericPair3.

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

  Module LongMessageHeader29.

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

  End LongMessageHeader29.

  Module MaximumThresholdPriceNumericPair3.

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

  End MaximumThresholdPriceNumericPair3.

  Module MinimumThresholdPriceNumericPair3.

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

  End MinimumThresholdPriceNumericPair3.

  Module TickIncrementNumericPair4.

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

  End TickIncrementNumericPair4.

  Module TickIncrementRawPair4.

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

  End TickIncrementRawPair4.

  Module LongMessageHeader30.

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

  End LongMessageHeader30.

  Module StrikePriceNumericPair14.

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

  End StrikePriceNumericPair14.

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

  Module NetChangeNumericPair4.

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

  End NetChangeNumericPair4.

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

  Module LongMessageHeader31.

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

  End LongMessageHeader31.

  Module StrikePriceNumericPair15.

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

  End StrikePriceNumericPair15.

  Module BidPriceSummaryNumericPair2.

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

  End BidPriceSummaryNumericPair2.

  Module AskPriceSummaryNumericPair2.

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

  End AskPriceSummaryNumericPair2.

  Module LastPriceNumericPair2.

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

  End LastPriceNumericPair2.

  Module NetChangeNumericPair5.

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

  End NetChangeNumericPair5.

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

  Module HighPriceNumericPair2.

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

  End HighPriceNumericPair2.

  Module LowPriceNumericPair2.

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

  End LowPriceNumericPair2.

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

  Module PreviousSettlementPriceNumericPair2.

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

  End PreviousSettlementPriceNumericPair2.

  Module LongMessageHeader32.

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

  End LongMessageHeader32.

  Module FutureProduct8.

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

  End FutureProduct8.

  Module BidPriceSummaryNumericPair3.

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

  End BidPriceSummaryNumericPair3.

  Module AskPriceSummaryNumericPair3.

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

  End AskPriceSummaryNumericPair3.

  Module LastPriceNumericPair3.

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

  End LastPriceNumericPair3.

  Module OpenPriceNumericPair2.

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

  End OpenPriceNumericPair2.

  Module HighPriceNumericPair3.

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

  End HighPriceNumericPair3.

  Module LowPriceNumericPair3.

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

  End LowPriceNumericPair3.

  Module SettlementPriceFutureOptionsSummaryMessageNumericPair2.

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

  End SettlementPriceFutureOptionsSummaryMessageNumericPair2.

  Module NetChangeNumericPair6.

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

  End NetChangeNumericPair6.

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

  Module LongMessageHeader33.

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

  End LongMessageHeader33.

  Module BidPriceSummaryNumericPair4.

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

  End BidPriceSummaryNumericPair4.

  Module AskPriceSummaryNumericPair4.

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

  End AskPriceSummaryNumericPair4.

  Module LastPriceNumericPair4.

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

  End LastPriceNumericPair4.

  Module OpenPriceNumericPair3.

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

  End OpenPriceNumericPair3.

  Module HighPriceNumericPair4.

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

  End HighPriceNumericPair4.

  Module LowPriceNumericPair4.

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

  End LowPriceNumericPair4.

  Module NetChangeNumericPair7.

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

  End NetChangeNumericPair7.

  Module LongMessageHeader34.

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

  End LongMessageHeader34.

  Module BeginningOfOptionsSummaryMessage.

    (** This message indicates that the beginning and the end of day N: Option Summary messages are to follow. Other messages (such as bulletins) can be interspersed with the summaries. *)
    Record t := {
      long_message_header : LongMessageHeader34.t;
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader34.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader34.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader34.decode bytes with
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
      rewrite !length_app, !LongMessageHeader34.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader34.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader34.eq_dec]. Defined.

  End BeginningOfOptionsSummaryMessage.

  Module LongMessageHeader35.

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

  End LongMessageHeader35.

  Module BeginningOfFutureOptionsSummaryMessage.

    (** This message indicates that the beginning and the end of day NB: Future Options Summary messages are to follow. Other messages (such as bulletins) can be interspersed with the summaries. *)
    Record t := {
      long_message_header : LongMessageHeader35.t;
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader35.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader35.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader35.decode bytes with
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
      rewrite !length_app, !LongMessageHeader35.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader35.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader35.eq_dec]. Defined.

  End BeginningOfFutureOptionsSummaryMessage.

  Module LongMessageHeader36.

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

  End LongMessageHeader36.

  Module BeginningOfFuturesSummaryMessage.

    (** This message indicates that the beginning or end-of-day NF: Future Summary messages are to follow. Other messages can be interspersed with the summaries. *)
    Record t := {
      long_message_header : LongMessageHeader36.t;
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader36.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader36.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader36.decode bytes with
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
      rewrite !length_app, !LongMessageHeader36.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader36.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader36.eq_dec]. Defined.

  End BeginningOfFuturesSummaryMessage.

  Module LongMessageHeader37.

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

  End LongMessageHeader37.

  Module BeginningOfStrategySummaryMessage.

    (** This message indicates that the beginning or the end of day NS: Strategy Summary messages are to follow. Other messages can be interspersed with the summaries. *)
    Record t := {
      long_message_header : LongMessageHeader37.t;
      exchange_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader37.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader37.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader37.decode bytes with
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
      rewrite !length_app, !LongMessageHeader37.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader37.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader37.eq_dec]. Defined.

  End BeginningOfStrategySummaryMessage.

  Module LongMessageHeader38.

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

  End LongMessageHeader38.

  Module FutureProduct9.

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

  End FutureProduct9.

  Module TradePriceNumericPair8.

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

  End TradePriceNumericPair8.

  Module NetChangeNumericPair8.

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

  End NetChangeNumericPair8.

  Module LongMessageHeader39.

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

  End LongMessageHeader39.

  Module GroupStatusMessage.

    (** This message will be sent when a group of trading instruments enters a new status. *)
    Record t := {
      long_message_header : LongMessageHeader39.t;
      exchange_id : list byte;
      root_symbol_group : list byte;
      group_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader39.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (root_symbol_group record) = 6 /\
      Datatypes.length (group_status record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader39.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (root_symbol_group record) ++
      encode_bytes 1 (group_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader39.decode bytes with
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
      rewrite !length_app, !LongMessageHeader39.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader39.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader39.eq_dec]. Defined.

  End GroupStatusMessage.

  Module LongMessageHeader40.

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

  End LongMessageHeader40.

  Module GroupStatusStrategiesMessage.

    (** This message will be sent when a strategy group of trading instruments enters a new status. All strategies have a predetermined group that can be found in the JS: Strategy Instrument Keys message. *)
    Record t := {
      long_message_header : LongMessageHeader40.t;
      exchange_id : list byte;
      group_instrument : list byte;
      group_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader40.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (group_instrument record) = 2 /\
      Datatypes.length (group_status record) = 1.

    Definition encode (record : t) : list byte :=
      LongMessageHeader40.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 2 (group_instrument record) ++
      encode_bytes 1 (group_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader40.decode bytes with
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
      rewrite !length_app, !LongMessageHeader40.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader40.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader40.eq_dec]. Defined.

  End GroupStatusStrategiesMessage.

  Module LongMessageHeader41.

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

  End LongMessageHeader41.

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

  Module LongMessageHeader42.

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

  End LongMessageHeader42.

  Module EndOfSalesMessage.

    (** The S: End of Sales message is sent when there is no more trading activity to be transmitted. This occurs after the closing of the market. *)
    Record t := {
      long_message_header : LongMessageHeader42.t;
      reserved : N;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader42.bounded (long_message_header record) /\
      (reserved record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader42.encode (long_message_header record) ++
      encode_uint 1 (reserved record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader42.decode bytes with
      | None => None
      | Some (long_message_header_value, bytes) =>
          match decode_uint 1 bytes with
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
      rewrite !length_app, !LongMessageHeader42.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader42.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader42.eq_dec]. Defined.

  End EndOfSalesMessage.

  Module LongMessageHeader43.

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

  End LongMessageHeader43.

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

  Module LongMessageHeader44.

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

  End LongMessageHeader44.

  Module EndOfTransmissionMessage.

    (** This message will be sent daily to indicate that the day’s transmission is complete. No HSVF messages will be transmitted afterwards. Transmission will resume the following day. *)
    Record t := {
      long_message_header : LongMessageHeader44.t;
      exchange_id : list byte;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader44.bounded (long_message_header record) /\
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader44.encode (long_message_header record) ++
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader44.decode bytes with
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
      rewrite !length_app, !LongMessageHeader44.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader44.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader44.eq_dec]. Defined.

  End EndOfTransmissionMessage.

  Module LongMessageHeader45.

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

  End LongMessageHeader45.

  Module CircuitAssuranceMessage.

    (** This message is sent out if no messages are sent by SAM for more than one minute after the broadcast has started (i.e., at the termination of the Test Loop message). This will be an assurance that the line is up. This message will continue to be sent until the U: End of Transmission message is sent. The Circuit Assurance message will repeat the sequence number of the previous record transmitted (except if it is a re-transmit message), i.e. it will not increase the sequence number. *)
    Record t := {
      long_message_header : LongMessageHeader45.t;
      time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      LongMessageHeader45.bounded (long_message_header record) /\
      Datatypes.length (time record) = 6.

    Definition encode (record : t) : list byte :=
      LongMessageHeader45.encode (long_message_header record) ++
      encode_bytes 6 (time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match LongMessageHeader45.decode bytes with
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
      rewrite !length_app, !LongMessageHeader45.encode_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite LongMessageHeader45.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply LongMessageHeader45.eq_dec]. Defined.

  End CircuitAssuranceMessage.

End MxSolaMulticastV1122.
