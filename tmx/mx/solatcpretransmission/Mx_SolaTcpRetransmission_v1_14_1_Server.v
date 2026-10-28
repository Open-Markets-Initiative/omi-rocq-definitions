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
      - a Composite rule
      - a run counted by a field
  *)

Module MxSolaTcpRetransmissionV1141Server.

  Module MessageHeader.

    (** Standard Hsvf message header *)
    Record t := {
      sequence_number : list byte;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (sequence_number record) = 10 /\
      Datatypes.length (message_type record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (sequence_number record) ++
      encode_bytes 2 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (sequence_number_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| sequence_number := sequence_number_value; message_type := message_type_value |}, bytes)
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

  Module FutureProduct.

    (** Future product symbology *)
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

  Module NetChangeFuturesTradeMessageNumericPair.

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

  End NetChangeFuturesTradeMessageNumericPair.

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

  Module FutureProduct2.

    (** Future product symbology *)
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

  Module FutureRequestForQuoteMessage.

    (** Futures Request for Quote message *)
    Record t := {
      exchange_id : list byte;
      future_product : FutureProduct2.t;
      requested_size : list byte;
      requested_market_side : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      FutureProduct2.bounded (future_product record) /\
      Datatypes.length (requested_size record) = 8 /\
      Datatypes.length (requested_market_side record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      FutureProduct2.encode (future_product record) ++
      encode_bytes 8 (requested_size record) ++
      encode_bytes 1 (requested_market_side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                      Some ({| exchange_id := exchange_id_value; future_product := future_product_value; requested_size := requested_size_value; requested_market_side := requested_market_side_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !FutureProduct2.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite FutureProduct2.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply FutureProduct2.eq_dec]. Defined.

  End FutureRequestForQuoteMessage.

  Module StrategyRequestForQuoteMessage.

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

  End StrategyRequestForQuoteMessage.

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

  Module FutureProduct3.

    (** Future product symbology *)
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
      exchange_id : list byte;
      future_product : FutureProduct3.t;
      series_status : list byte;
      scheduled_status_change_time : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      FutureProduct3.bounded (future_product record) /\
      Datatypes.length (series_status record) = 1 /\
      Datatypes.length (scheduled_status_change_time record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      FutureProduct3.encode (future_product record) ++
      encode_bytes 1 (series_status record) ++
      encode_bytes 6 (scheduled_status_change_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
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
                      Some ({| exchange_id := exchange_id_value; future_product := future_product_value; series_status := series_status_value; scheduled_status_change_time := scheduled_status_change_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !FutureProduct3.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite FutureProduct3.decode_encode by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply FutureProduct3.eq_dec]. Defined.

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

  Module FutureProduct4.

    (** Future product symbology *)
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

  Module BidPriceQuoteFuturesQuoteMessageOpeningPair.

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

  End BidPriceQuoteFuturesQuoteMessageOpeningPair.

  Module BidPriceQuoteFuturesQuoteMessageNumericPair.

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

  End BidPriceQuoteFuturesQuoteMessageNumericPair.

  Module AskPriceQuoteFuturesQuoteMessageOpeningPair.

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

  End AskPriceQuoteFuturesQuoteMessageOpeningPair.

  Module AskPriceQuoteFuturesQuoteMessageNumericPair.

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

  End AskPriceQuoteFuturesQuoteMessageNumericPair.

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

  Module BidPriceQuoteMarketDepthLevelOpeningPair.

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

  End BidPriceQuoteMarketDepthLevelOpeningPair.

  Module BidPriceQuoteMarketDepthLevelNumericPair.

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

  End BidPriceQuoteMarketDepthLevelNumericPair.

  Module AskPriceQuoteMarketDepthLevelOpeningPair.

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

  End AskPriceQuoteMarketDepthLevelOpeningPair.

  Module AskPriceQuoteMarketDepthLevelNumericPair.

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

  End AskPriceQuoteMarketDepthLevelNumericPair.

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

  Module BidPriceQuoteMarketDepthLevelHBOpeningPair.

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

  End BidPriceQuoteMarketDepthLevelHBOpeningPair.

  Module BidPriceQuoteMarketDepthLevelHBNumericPair.

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

  End BidPriceQuoteMarketDepthLevelHBNumericPair.

  Module AskPriceQuoteMarketDepthLevelHBOpeningPair.

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

  End AskPriceQuoteMarketDepthLevelHBOpeningPair.

  Module AskPriceQuoteMarketDepthLevelHBNumericPair.

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

  End AskPriceQuoteMarketDepthLevelHBNumericPair.

  Module FutureProduct5.

    (** Future product symbology *)
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

  Module BidPriceQuoteMarketDepthLevelHFOpeningPair.

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

  End BidPriceQuoteMarketDepthLevelHFOpeningPair.

  Module BidPriceQuoteMarketDepthLevelHFNumericPair.

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

  End BidPriceQuoteMarketDepthLevelHFNumericPair.

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

  Module BidPriceQuoteStrategyMarketDepthLevelOpeningPair.

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

  End BidPriceQuoteStrategyMarketDepthLevelOpeningPair.

  Module BidPriceQuoteStrategyMarketDepthLevelNumericPair.

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

  End BidPriceQuoteStrategyMarketDepthLevelNumericPair.

  Module AskPriceQuoteStrategyMarketDepthLevelOpeningPair.

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

  End AskPriceQuoteStrategyMarketDepthLevelOpeningPair.

  Module AskPriceQuoteStrategyMarketDepthLevelNumericPair.

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

  End AskPriceQuoteStrategyMarketDepthLevelNumericPair.

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

  Module FutureProduct6.

    (** Future product symbology *)
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

  Module MinimumThresholdPriceInstrumentNumericPair.

    Record t := {
      minimum_threshold_price_instrument : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (minimum_threshold_price_instrument record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (minimum_threshold_price_instrument record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (minimum_threshold_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| minimum_threshold_price_instrument := minimum_threshold_price_instrument_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceInstrumentNumericPair.

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

  Module MinimumThresholdPriceInstrumentNumericPair2.

    Record t := {
      minimum_threshold_price_instrument : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (minimum_threshold_price_instrument record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (minimum_threshold_price_instrument record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (minimum_threshold_price_instrument_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| minimum_threshold_price_instrument := minimum_threshold_price_instrument_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceInstrumentNumericPair2.

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

  Module UnderlyingInstrumentKeysMessage.

    (** The 'Underlying Instrument Keys' message will be the first messages sent during the day. There is no 'Underlying Summary' message attached to the 'Instrument Keys' messages *)
    Record t := {
      exchange_id : list byte;
      group_instrument : list byte;
      instrument : list byte;
      instrument_external_code : list byte;
      market_flow_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (group_instrument record) = 2 /\
      Datatypes.length (instrument record) = 4 /\
      Datatypes.length (instrument_external_code record) = 30 /\
      Datatypes.length (market_flow_indicator record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 2 (group_instrument record) ++
      encode_bytes 4 (instrument record) ++
      encode_bytes 30 (instrument_external_code record) ++
      encode_bytes 2 (market_flow_indicator record).

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
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (market_flow_indicator_value, bytes) =>
                          Some ({| exchange_id := exchange_id_value; group_instrument := group_instrument_value; instrument := instrument_value; instrument_external_code := instrument_external_code_value; market_flow_indicator := market_flow_indicator_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnderlyingInstrumentKeysMessage.

  Module FutureProduct7.

    (** Future product symbology *)
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
      root : list byte;
      symbol_month : list byte;
      symbol_year : list byte;
      expiry_day : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (root record) = 6 /\
      Datatypes.length (symbol_month record) = 1 /\
      Datatypes.length (symbol_year record) = 2 /\
      Datatypes.length (expiry_day record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (root record) ++
      encode_bytes 1 (symbol_month record) ++
      encode_bytes 2 (symbol_year record) ++
      encode_bytes 2 (expiry_day record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (root_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (symbol_month_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (symbol_year_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (expiry_day_value, bytes) =>
                      Some ({| root := root_value; symbol_month := symbol_month_value; symbol_year := symbol_year_value; expiry_day := expiry_day_value |}, bytes)
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

  Module MinimumThresholdPriceStrategyNumericPair.

    Record t := {
      minimum_threshold_price_strategy : list byte;
      minimum_threshold_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (minimum_threshold_price_strategy record) = 7 /\
      Datatypes.length (minimum_threshold_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (minimum_threshold_price_strategy record) ++
      encode_bytes 1 (minimum_threshold_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (minimum_threshold_price_strategy_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (minimum_threshold_price_fraction_indicator_value, bytes) =>
              Some ({| minimum_threshold_price_strategy := minimum_threshold_price_strategy_value; minimum_threshold_price_fraction_indicator := minimum_threshold_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MinimumThresholdPriceStrategyNumericPair.

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

  Module LegRatioOrDeltaNumericPair.

    Record t := {
      leg_ratio_or_delta : list byte;
      leg_ratio_or_delta_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (leg_ratio_or_delta record) = 4 /\
      Datatypes.length (leg_ratio_or_delta_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 4 (leg_ratio_or_delta record) ++
      encode_bytes 1 (leg_ratio_or_delta_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 4 bytes with
      | None => None
      | Some (leg_ratio_or_delta_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (leg_ratio_or_delta_fraction_indicator_value, bytes) =>
              Some ({| leg_ratio_or_delta := leg_ratio_or_delta_value; leg_ratio_or_delta_fraction_indicator := leg_ratio_or_delta_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LegRatioOrDeltaNumericPair.

  Module LegPriceNumericPair.

    Record t := {
      leg_price : list byte;
      leg_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (leg_price record) = 7 /\
      Datatypes.length (leg_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (leg_price record) ++
      encode_bytes 1 (leg_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (leg_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (leg_price_fraction_indicator_value, bytes) =>
              Some ({| leg_price := leg_price_value; leg_price_fraction_indicator := leg_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LegPriceNumericPair.

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

  Module InitialOrderPriceNumericPair.

    Record t := {
      initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (initial_order_price record) = 7 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| initial_order_price := initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
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

  Module InitialOrderPriceNumericPair2.

    Record t := {
      initial_order_price : list byte;
      initial_order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (initial_order_price record) = 7 /\
      Datatypes.length (initial_order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (initial_order_price record) ++
      encode_bytes 1 (initial_order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (initial_order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (initial_order_price_fraction_indicator_value, bytes) =>
              Some ({| initial_order_price := initial_order_price_value; initial_order_price_fraction_indicator := initial_order_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
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

  Module NetChangeOptionSummaryMessageNumericPair.

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

  End NetChangeOptionSummaryMessageNumericPair.

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

  Module ClosingPriceNumericPair.

    Record t := {
      closing_price : list byte;
      closing_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (closing_price record) = 7 /\
      Datatypes.length (closing_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (closing_price record) ++
      encode_bytes 1 (closing_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (closing_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (closing_price_fraction_indicator_value, bytes) =>
              Some ({| closing_price := closing_price_value; closing_price_fraction_indicator := closing_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClosingPriceNumericPair.

  Module PreviousClosingPriceNumericPair.

    Record t := {
      previous_closing_price : list byte;
      previous_closing_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (previous_closing_price record) = 7 /\
      Datatypes.length (previous_closing_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (previous_closing_price record) ++
      encode_bytes 1 (previous_closing_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (previous_closing_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (previous_closing_price_fraction_indicator_value, bytes) =>
              Some ({| previous_closing_price := previous_closing_price_value; previous_closing_price_fraction_indicator := previous_closing_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PreviousClosingPriceNumericPair.

  Module StrikePriceNumericPair16.

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

  End StrikePriceNumericPair16.

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

  Module NetChangeFutureOptionsSummaryMessageNumericPair.

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

  End NetChangeFutureOptionsSummaryMessageNumericPair.

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

  Module FutureProduct8.

    (** Future product symbology *)
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

  Module SettlementPriceNumericPair2.

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

  End SettlementPriceNumericPair2.

  Module NetChangeFuturesSummaryMessageNumericPair.

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

  End NetChangeFuturesSummaryMessageNumericPair.

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

  Module NetChangeStrategySummaryMessageNumericPair.

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

  End NetChangeStrategySummaryMessageNumericPair.

  Module StrikePriceNumericPair17.

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

  End StrikePriceNumericPair17.

  Module OrderPriceNumericPair.

    Record t := {
      order_price : list byte;
      order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_price record) = 7 /\
      Datatypes.length (order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (order_price record) ++
      encode_bytes 1 (order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (order_price_fraction_indicator_value, bytes) =>
              Some ({| order_price := order_price_value; order_price_fraction_indicator := order_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderPriceNumericPair.

  Module OrderPriceNumericPair2.

    Record t := {
      order_price : list byte;
      order_price_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (order_price record) = 7 /\
      Datatypes.length (order_price_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (order_price record) ++
      encode_bytes 1 (order_price_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (order_price_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (order_price_fraction_indicator_value, bytes) =>
              Some ({| order_price := order_price_value; order_price_fraction_indicator := order_price_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderPriceNumericPair2.

  Module BeginningOfOptionsSummaryMessage.

    (** This message indicates that the beginning and the end of day N: Option Summary messages are to follow. Other messages (such as bulletins) can be interspersed with the summaries. *)
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

    (** This message indicates that the beginning and the end of day NB: Future Options Summary messages are to follow. Other messages (such as bulletins) can be interspersed with the summaries. *)
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

    (** This message indicates that the beginning or end-of-day NF: Future Summary messages are to follow. Other messages can be interspersed with the summaries. *)
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

    (** This message indicates that the beginning or the end of day NS: Strategy Summary messages are to follow. Other messages can be interspersed with the summaries. *)
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

  Module StrikePriceNumericPair18.

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

  End StrikePriceNumericPair18.

  Module StrategyAuctionEndingMessage.

    (** Strategy auction ending *)
    Record t := {
      exchange_id : list byte;
      strategy_symbol : list byte;
      auction_id : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (strategy_symbol record) = 30 /\
      Datatypes.length (auction_id record) = 6.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 30 (strategy_symbol record) ++
      encode_bytes 6 (auction_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 30 bytes with
          | None => None
          | Some (strategy_symbol_value, bytes) =>
              match decode_bytes 6 bytes with
              | None => None
              | Some (auction_id_value, bytes) =>
                  Some ({| exchange_id := exchange_id_value; strategy_symbol := strategy_symbol_value; auction_id := auction_id_value |}, bytes)
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

  End StrategyAuctionEndingMessage.

  Module FutureProduct9.

    (** Future product symbology *)
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

  Module TradePriceNumericPair9.

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

  End TradePriceNumericPair9.

  Module NetChangeFuturesTradeCorrectionMessageNumericPair.

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

  End NetChangeFuturesTradeCorrectionMessageNumericPair.

  Module GroupStatusMessage.

    (** This message will be sent when a group of trading instruments enters a new status. *)
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

    (** This message will be sent when a strategy group of trading instruments enters a new status. All strategies have a predetermined group that can be found in the JS: Strategy Instrument Keys message. *)
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

  Module FutureProduct10.

    (** Future product symbology *)
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

  End FutureProduct10.

  Module CouponNumericPair.

    Record t := {
      coupon : list byte;
      coupon_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (coupon record) = 7 /\
      Datatypes.length (coupon_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (coupon record) ++
      encode_bytes 1 (coupon_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (coupon_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (coupon_fraction_indicator_value, bytes) =>
              Some ({| coupon := coupon_value; coupon_fraction_indicator := coupon_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CouponNumericPair.

  Module ConversionFactorNumericPair.

    Record t := {
      conversion_factor : list byte;
      conversion_factor_fraction_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (conversion_factor record) = 7 /\
      Datatypes.length (conversion_factor_fraction_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 7 (conversion_factor record) ++
      encode_bytes 1 (conversion_factor_fraction_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 7 bytes with
      | None => None
      | Some (conversion_factor_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (conversion_factor_fraction_indicator_value, bytes) =>
              Some ({| conversion_factor := conversion_factor_value; conversion_factor_fraction_indicator := conversion_factor_fraction_indicator_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConversionFactorNumericPair.

  Module RegularTextBulletin.

    (** Regular Text Bulletin *)
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

  Module EndOfTransmissionMessage.

    (** This message will be sent daily to indicate that the day’s transmission is complete. No HSVF messages will be transmitted afterwards. Transmission will resume the following day. *)
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

    (** This message is sent out if no messages are sent by SAM for more than one minute after the broadcast has started (i.e., at the termination of the Test Loop message). This will be an assurance that the line is up. This message will continue to be sent until the U: End of Transmission message is sent. The Circuit Assurance message will repeat the sequence number of the previous record transmitted (except if it is a re-transmit message), i.e. it will not increase the sequence number *)
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

  Module StartOfDayMessage.

    (** This message is sent at the beginning of the day to provide the Business Date. *)
    Record t := {
      exchange_id : list byte;
      business_date : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (exchange_id record) = 1 /\
      Datatypes.length (business_date record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (exchange_id record) ++
      encode_bytes 8 (business_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (exchange_id_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (business_date_value, bytes) =>
              Some ({| exchange_id := exchange_id_value; business_date := business_date_value |}, bytes)
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

  End StartOfDayMessage.

End MxSolaTcpRetransmissionV1141Server.
