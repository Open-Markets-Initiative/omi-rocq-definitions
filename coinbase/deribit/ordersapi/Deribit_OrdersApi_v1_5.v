From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Coinbase Orders Api

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
      - a field present only on a condition
      - a block whose stated length holds more than its fields
      - a run counted by a field

    License: MIT No Attribution
  *)

Module DeribitOrdersApiV15.

  Module LogonMessage.

    (** LogonMessage *)
    Record t := {
      client_id : list byte;
      secret : list byte;
      reset_seq_num : N;
      schema_version : N;
      session_cancel_on_disconnect : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (client_id record) = 16 /\
      Datatypes.length (secret record) = 48 /\
      (reset_seq_num record < 256 ^ N.of_nat 1)%N /\
      (schema_version record < 256 ^ N.of_nat 2)%N /\
      (session_cancel_on_disconnect record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (client_id record) ++
      encode_bytes 48 (secret record) ++
      encode_uint 1 (reset_seq_num record) ++
      encode_uint_le 2 (schema_version record) ++
      encode_uint 1 (session_cancel_on_disconnect record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (client_id_value, bytes) =>
          match decode_bytes 48 bytes with
          | None => None
          | Some (secret_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reset_seq_num_value, bytes) =>
                  match decode_uint_le 2 bytes with
                  | None => None
                  | Some (schema_version_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (session_cancel_on_disconnect_value, bytes) =>
                          Some ({| client_id := client_id_value; secret := secret_value; reset_seq_num := reset_seq_num_value; schema_version := schema_version_value; session_cancel_on_disconnect := session_cancel_on_disconnect_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 68.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length, !encode_uint_le_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module LogonConfMessage.

    (** LogonConfMessage *)
    Record t := {
      heartbeat_interval_seconds : N;
      schema_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (heartbeat_interval_seconds record < 256 ^ N.of_nat 4)%N /\
      (schema_version record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (heartbeat_interval_seconds record) ++
      encode_uint_le 2 (schema_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (heartbeat_interval_seconds_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (schema_version_value, bytes) =>
              Some ({| heartbeat_interval_seconds := heartbeat_interval_seconds_value; schema_version := schema_version_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End LogonConfMessage.

  Module HeartbeatMessage.

    (** HeartbeatMessage *)
    Record t := {
      correlation_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          Some ({| correlation_id := correlation_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint_le by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End HeartbeatMessage.

  Module TestRequestMessage.

    (** TestRequestMessage *)
    Record t := {
      correlation_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          Some ({| correlation_id := correlation_id_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint_le by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TestRequestMessage.

  Module ResendRequestMessage.

    (** ResendRequestMessage *)
    Record t := {
      from_sequence_number : N;
      to_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (from_sequence_number record < 256 ^ N.of_nat 8)%N /\
      (to_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (from_sequence_number record) ++
      encode_uint_le 8 (to_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (from_sequence_number_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (to_sequence_number_value, bytes) =>
              Some ({| from_sequence_number := from_sequence_number_value; to_sequence_number := to_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ResendRequestMessage.

  Module GapFillMessage.

    (** GapFillMessage *)
    Record t := {
      new_sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_sequence_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (new_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (new_sequence_number_value, bytes) =>
          Some ({| new_sequence_number := new_sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint_le by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GapFillMessage.

  Module Quantity.

    (** NewOrderRequestMessage *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Quantity.

  Module ShowQty.

    (** NewOrderRequestMessage *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End ShowQty.

  Module CancelOrderRequestMessage.

    (** CancelOrderRequestMessage *)
    Record t := {
      client_order_id : N;
      correlation_id : N;
      instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (instrument_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; correlation_id := correlation_id_value; instrument_id := instrument_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End CancelOrderRequestMessage.

  Module CancelOrderByIdRequestMessage.

    (** CancelOrderByIdRequestMessage *)
    Record t := {
      order_id : N;
      correlation_id : N;
      instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (instrument_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (order_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  Some ({| order_id := order_id_value; correlation_id := correlation_id_value; instrument_id := instrument_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End CancelOrderByIdRequestMessage.

  Module GroupSizeEncoding.

    (** groupSizeEncoding *)
    Record t := {
      block_length : N;
      num_in_group : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (num_in_group record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (block_length record) ++
      encode_uint_le 2 (num_in_group record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (num_in_group_value, bytes) =>
              Some ({| block_length := block_length_value; num_in_group := num_in_group_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GroupSizeEncoding.

  Module BidQty.

    (** quotes *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BidQty.

  Module AskQty.

    (** quotes *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AskQty.

  Module MassCancelRequestMessage.

    (** MassCancelRequestMessage *)
    Record t := {
      correlation_id : N;
      currency_pair_id : N;
      instrument_id_optional : N;
      product_type : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (currency_pair_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id_optional record < 256 ^ N.of_nat 8)%N /\
      (product_type record < 256 ^ N.of_nat 1)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (currency_pair_id record) ++
      encode_uint_le 8 (instrument_id_optional record) ++
      encode_uint 1 (product_type record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (currency_pair_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (instrument_id_optional_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (product_type_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          Some ({| correlation_id := correlation_id_value; currency_pair_id := currency_pair_id_value; instrument_id_optional := instrument_id_optional_value; product_type := product_type_value; side := side_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MassCancelRequestMessage.

  Module MassQuoteCancelRequestMessage.

    (** MassQuoteCancelRequestMessage *)
    Record t := {
      correlation_id : N;
      mmp_group_id : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (mmp_group_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (mmp_group_id record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (mmp_group_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  Some ({| correlation_id := correlation_id_value; mmp_group_id := mmp_group_id_value; side := side_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MassQuoteCancelRequestMessage.

  Module GetMassQuoteMmpStatusRequestMessage.

    (** GetMassQuoteMmpStatusRequestMessage *)
    Record t := {
      correlation_id : N;
      mmp_group_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (mmp_group_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (mmp_group_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (mmp_group_id_value, bytes) =>
              Some ({| correlation_id := correlation_id_value; mmp_group_id := mmp_group_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GetMassQuoteMmpStatusRequestMessage.

  Module GetOrdersMmpStatusRequestMessage.

    (** GetOrdersMmpStatusRequestMessage *)
    Record t := {
      correlation_id : N;
      currency_pair_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (currency_pair_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (currency_pair_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (currency_pair_id_value, bytes) =>
              Some ({| correlation_id := correlation_id_value; currency_pair_id := currency_pair_id_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GetOrdersMmpStatusRequestMessage.

  Module TotalFilled.

    (** NewOrderResponseMessage *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TotalFilled.

  Module VisibleQty.

    (** NewOrderResponseMessage *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End VisibleQty.

  Module FillQty.

    (** fills *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End FillQty.

  Module CancelOrderResponseMessage.

    (** CancelOrderResponseMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      client_order_id : N;
      correlation_id : N;
      order_id : N;
      instrument_id : N;
      receive_time : N;
      quantity : Quantity.t;
      total_filled : TotalFilled.t;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      (receive_time record < 256 ^ N.of_nat 8)%N /\
      Quantity.bounded (quantity record) /\
      TotalFilled.bounded (total_filled record).

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (instrument_id record) ++
      encode_uint_le 8 (receive_time record) ++
      Quantity.encode (quantity record) ++
      TotalFilled.encode (total_filled record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (client_order_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (correlation_id_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (order_id_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (instrument_id_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (receive_time_value, bytes) =>
                                  match Quantity.decode bytes with
                                  | None => None
                                  | Some (quantity_value, bytes) =>
                                      match TotalFilled.decode bytes with
                                      | None => None
                                      | Some (total_filled_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; exec_id := exec_id_value; client_order_id := client_order_id_value; correlation_id := correlation_id_value; order_id := order_id_value; instrument_id := instrument_id_value; receive_time := receive_time_value; quantity := quantity_value; total_filled := total_filled_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 74.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !Quantity.encode_length, !TotalFilled.encode_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite Quantity.decode_encode by exact bound_7.
      rewrite TotalFilled.decode_encode by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply Quantity.eq_dec | apply TotalFilled.eq_dec]. Defined.

  End CancelOrderResponseMessage.

  Module BidFilledQty.

    (** quotes *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BidFilledQty.

  Module AskFilledQty.

    (** quotes *)
    Record t := {
      mantissa : N;
      exponent : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (mantissa record < 256 ^ N.of_nat 8)%N /\
      (exponent record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (mantissa record) ++
      encode_uint 1 (exponent record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (mantissa_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (exponent_value, bytes) =>
              Some ({| mantissa := mantissa_value; exponent := exponent_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AskFilledQty.

  Module MassCancelResponseMessage.

    (** MassCancelResponseMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      correlation_id : N;
      receive_time : N;
      total_order_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (receive_time record < 256 ^ N.of_nat 8)%N /\
      (total_order_count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (receive_time record) ++
      encode_uint_le 4 (total_order_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (correlation_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (receive_time_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (total_order_count_value, bytes) =>
                          Some ({| timestamp := timestamp_value; exec_id := exec_id_value; correlation_id := correlation_id_value; receive_time := receive_time_value; total_order_count := total_order_count_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MassCancelResponseMessage.

  Module GetMassQuoteMmpStatusResponseMessage.

    (** GetMassQuoteMmpStatusResponseMessage *)
    Record t := {
      timestamp : N;
      correlation_id : N;
      mmp_group_id : N;
      frozen_until_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (mmp_group_id record < 256 ^ N.of_nat 8)%N /\
      (frozen_until_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (mmp_group_id record) ++
      encode_uint_le 8 (frozen_until_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (mmp_group_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (frozen_until_time_value, bytes) =>
                      Some ({| timestamp := timestamp_value; correlation_id := correlation_id_value; mmp_group_id := mmp_group_id_value; frozen_until_time := frozen_until_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GetMassQuoteMmpStatusResponseMessage.

  Module GetMassQuoteMmpStatusRejectMessage.

    (** GetMassQuoteMmpStatusRejectMessage *)
    Record t := {
      timestamp : N;
      correlation_id : N;
      reason_mmp_status_reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (reason_mmp_status_reject_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint 1 (reason_mmp_status_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reason_mmp_status_reject_reason_value, bytes) =>
                  Some ({| timestamp := timestamp_value; correlation_id := correlation_id_value; reason_mmp_status_reject_reason := reason_mmp_status_reject_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GetMassQuoteMmpStatusRejectMessage.

  Module GetOrdersMmpStatusResponseMessage.

    (** GetOrdersMmpStatusResponseMessage *)
    Record t := {
      timestamp : N;
      correlation_id : N;
      currency_pair_id : N;
      frozen_until_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (currency_pair_id record < 256 ^ N.of_nat 8)%N /\
      (frozen_until_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (currency_pair_id record) ++
      encode_uint_le 8 (frozen_until_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (currency_pair_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (frozen_until_time_value, bytes) =>
                      Some ({| timestamp := timestamp_value; correlation_id := correlation_id_value; currency_pair_id := currency_pair_id_value; frozen_until_time := frozen_until_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GetOrdersMmpStatusResponseMessage.

  Module GetOrdersMmpStatusRejectMessage.

    (** GetOrdersMmpStatusRejectMessage *)
    Record t := {
      timestamp : N;
      correlation_id : N;
      reason_mmp_status_reject_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (reason_mmp_status_reject_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint 1 (reason_mmp_status_reject_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reason_mmp_status_reject_reason_value, bytes) =>
                  Some ({| timestamp := timestamp_value; correlation_id := correlation_id_value; reason_mmp_status_reject_reason := reason_mmp_status_reject_reason_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End GetOrdersMmpStatusRejectMessage.

  Module MassQuoteMmpTriggeredMessage.

    (** MassQuoteMmpTriggeredMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      mmp_group_id : N;
      frozen_until : N;
      quantity_level : N;
      vega_level : N;
      delta_level : N;
      trigger : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (mmp_group_id record < 256 ^ N.of_nat 8)%N /\
      (frozen_until record < 256 ^ N.of_nat 8)%N /\
      (quantity_level record < 256 ^ N.of_nat 8)%N /\
      (vega_level record < 256 ^ N.of_nat 8)%N /\
      (delta_level record < 256 ^ N.of_nat 8)%N /\
      (trigger record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (mmp_group_id record) ++
      encode_uint_le 8 (frozen_until record) ++
      encode_uint_le 8 (quantity_level record) ++
      encode_uint_le 8 (vega_level record) ++
      encode_uint_le 8 (delta_level record) ++
      encode_uint 1 (trigger record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (mmp_group_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (frozen_until_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (quantity_level_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (vega_level_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (delta_level_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (trigger_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; exec_id := exec_id_value; mmp_group_id := mmp_group_id_value; frozen_until := frozen_until_value; quantity_level := quantity_level_value; vega_level := vega_level_value; delta_level := delta_level_value; trigger := trigger_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MassQuoteMmpTriggeredMessage.

  Module OrdersMmpTriggeredMessage.

    (** OrdersMmpTriggeredMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      currency_pair_id : N;
      frozen_until : N;
      quantity_level : N;
      vega_level : N;
      delta_level : N;
      trigger : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (currency_pair_id record < 256 ^ N.of_nat 8)%N /\
      (frozen_until record < 256 ^ N.of_nat 8)%N /\
      (quantity_level record < 256 ^ N.of_nat 8)%N /\
      (vega_level record < 256 ^ N.of_nat 8)%N /\
      (delta_level record < 256 ^ N.of_nat 8)%N /\
      (trigger record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (currency_pair_id record) ++
      encode_uint_le 8 (frozen_until record) ++
      encode_uint_le 8 (quantity_level record) ++
      encode_uint_le 8 (vega_level record) ++
      encode_uint_le 8 (delta_level record) ++
      encode_uint 1 (trigger record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (currency_pair_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (frozen_until_value, bytes) =>
                      match decode_uint_le 8 bytes with
                      | None => None
                      | Some (quantity_level_value, bytes) =>
                          match decode_uint_le 8 bytes with
                          | None => None
                          | Some (vega_level_value, bytes) =>
                              match decode_uint_le 8 bytes with
                              | None => None
                              | Some (delta_level_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (trigger_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; exec_id := exec_id_value; currency_pair_id := currency_pair_id_value; frozen_until := frozen_until_value; quantity_level := quantity_level_value; vega_level := vega_level_value; delta_level := delta_level_value; trigger := trigger_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrdersMmpTriggeredMessage.

  Module MassQuoteMmpUnfrozenMessage.

    (** MassQuoteMmpUnfrozenMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      mmp_group_id : N;
      correlation_id_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (mmp_group_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id_optional record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (mmp_group_id record) ++
      encode_uint_le 8 (correlation_id_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (mmp_group_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (correlation_id_optional_value, bytes) =>
                      Some ({| timestamp := timestamp_value; exec_id := exec_id_value; mmp_group_id := mmp_group_id_value; correlation_id_optional := correlation_id_optional_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MassQuoteMmpUnfrozenMessage.

  Module OrdersMmpUnfrozenMessage.

    (** OrdersMmpUnfrozenMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      currency_pair_id : N;
      correlation_id_optional : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (currency_pair_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id_optional record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (currency_pair_id record) ++
      encode_uint_le 8 (correlation_id_optional record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (currency_pair_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (correlation_id_optional_value, bytes) =>
                      Some ({| timestamp := timestamp_value; exec_id := exec_id_value; currency_pair_id := currency_pair_id_value; correlation_id_optional := correlation_id_optional_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrdersMmpUnfrozenMessage.

End DeribitOrdersApiV15.
