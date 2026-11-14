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
      - the dispatch that chooses a message by its type
      - a field present only on a condition
      - a block whose stated length holds more than its fields

    License: MIT No Attribution
  *)

Module CoinbaseDerivativesOrdersApiV13.

  Module LogonMessage.

    (** LogonMessage *)
    Record t := {
      username : list byte;
      password : list byte;
      reset_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 16 /\
      Datatypes.length (password record) = 32 /\
      (reset_seq_num record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (username record) ++
      encode_bytes 32 (password record) ++
      encode_uint 1 (reset_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (username_value, bytes) =>
          match decode_bytes 32 bytes with
          | None => None
          | Some (password_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (reset_seq_num_value, bytes) =>
                  Some ({| username := username_value; password := password_value; reset_seq_num := reset_seq_num_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 49.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LogonMessage.

  Module LogonConfMessage.

    (** LogonConfMessage *)
    Record t := {
      heartbeat_interval_seconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (heartbeat_interval_seconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (heartbeat_interval_seconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (heartbeat_interval_seconds_value, bytes) =>
          Some ({| heartbeat_interval_seconds := heartbeat_interval_seconds_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End LogonConfMessage.

  Module LogoutMessage.

    (** LogoutMessage *)
    Record t := {
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 64.

    Definition encode (record : t) : list byte :=
      encode_bytes 64 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 64 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          Some ({| reason := reason_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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

  End LogoutMessage.

  Module LoggedOutMessage.

    (** LoggedOutMessage *)
    Record t := {
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reason record) = 64.

    Definition encode (record : t) : list byte :=
      encode_bytes 64 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 64 bytes with
      | None => None
      | Some (reason_value, bytes) =>
          Some ({| reason := reason_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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

  End LoggedOutMessage.

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
      (from_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (to_sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (from_sequence_number record) ++
      encode_uint_le 4 (to_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (from_sequence_number_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (to_sequence_number_value, bytes) =>
              Some ({| from_sequence_number := from_sequence_number_value; to_sequence_number := to_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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
      gap_fill_padding : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_sequence_number record < 256 ^ N.of_nat 4)%N /\
      (gap_fill_padding record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (new_sequence_number record) ++
      encode_uint_le 4 (gap_fill_padding record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (new_sequence_number_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (gap_fill_padding_value, bytes) =>
              Some ({| new_sequence_number := new_sequence_number_value; gap_fill_padding := gap_fill_padding_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End GapFillMessage.

  Module InstrumentInfoRequestMessage.

    (** InstrumentInfoRequestMessage *)
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

  End InstrumentInfoRequestMessage.

  Module InstrumentInfoMessage.

    (** InstrumentInfoMessage *)
    Record t := {
      correlation_id : N;
      instrument_id : N;
      security_type : N;
      instrument_status : N;
      is_last_message : N;
      reserved_byte : N;
      symbol : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (security_type record < 256 ^ N.of_nat 1)%N /\
      (instrument_status record < 256 ^ N.of_nat 1)%N /\
      (is_last_message record < 256 ^ N.of_nat 1)%N /\
      (reserved_byte record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (symbol record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (security_type record) ++
      encode_uint 1 (instrument_status record) ++
      encode_uint 1 (is_last_message record) ++
      encode_uint 1 (reserved_byte record) ++
      encode_bytes 32 (symbol record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (instrument_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (security_type_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (instrument_status_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (is_last_message_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_byte_value, bytes) =>
                              match decode_bytes 32 bytes with
                              | None => None
                              | Some (symbol_value, bytes) =>
                                  Some ({| correlation_id := correlation_id_value; instrument_id := instrument_id_value; security_type := security_type_value; instrument_status := instrument_status_value; is_last_message := is_last_message_value; reserved_byte := reserved_byte_value; symbol := symbol_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentInfoMessage.

  Module SetAccountMessage.

    (** SetAccountMessage *)
    Record t := {
      correlation_id : N;
      account : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (account record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_bytes 16 (account record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (account_value, bytes) =>
              Some ({| correlation_id := correlation_id_value; account := account_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SetAccountMessage.

  Module SetTraderMessage.

    (** SetTraderMessage *)
    Record t := {
      correlation_id : N;
      trader : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trader record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_bytes 16 (trader record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (trader_value, bytes) =>
              Some ({| correlation_id := correlation_id_value; trader := trader_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SetTraderMessage.

  Module SetAckMessage.

    (** SetAckMessage *)
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

  End SetAckMessage.

  Module NewOrderMessage.

    (** NewOrderMessage *)
    Record t := {
      client_order_id : N;
      correlation_id : N;
      limit_price : N;
      quantity : N;
      instrument_id : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (limit_price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (limit_price record) ++
      encode_uint_le 4 (quantity record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (limit_price_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              Some ({| client_order_id := client_order_id_value; correlation_id := correlation_id_value; limit_price := limit_price_value; quantity := quantity_value; instrument_id := instrument_id_value; side := side_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End NewOrderMessage.

  Module OrderEnteredMessage.

    (** OrderEnteredMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      client_order_id : N;
      correlation_id : N;
      order_id : N;
      receive_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (receive_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (receive_time record).

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
                          | Some (receive_time_value, bytes) =>
                              Some ({| timestamp := timestamp_value; exec_id := exec_id_value; client_order_id := client_order_id_value; correlation_id := correlation_id_value; order_id := order_id_value; receive_time := receive_time_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderEnteredMessage.

  Module ReplaceOrderMessage.

    (** ReplaceOrderMessage *)
    Record t := {
      client_order_id : N;
      correlation_id : N;
      new_limit_price : N;
      new_quantity : N;
      instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (new_limit_price record < 256 ^ N.of_nat 8)%N /\
      (new_quantity record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (new_limit_price record) ++
      encode_uint_le 4 (new_quantity record) ++
      encode_uint_le 4 (instrument_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (new_limit_price_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (new_quantity_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          Some ({| client_order_id := client_order_id_value; correlation_id := correlation_id_value; new_limit_price := new_limit_price_value; new_quantity := new_quantity_value; instrument_id := instrument_id_value |}, bytes)
                      end
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

  End ReplaceOrderMessage.

  Module StreamOrderMessage.

    (** StreamOrderMessage *)
    Record t := {
      client_order_id : N;
      correlation_id : N;
      last_processed_fill_id : N;
      limit_price : N;
      quantity : N;
      instrument_id : N;
      side : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (last_processed_fill_id record < 256 ^ N.of_nat 8)%N /\
      (limit_price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (last_processed_fill_id record) ++
      encode_uint_le 8 (limit_price record) ++
      encode_uint_le 4 (quantity record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (side record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (last_processed_fill_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (limit_price_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint_le 4 bytes with
                          | None => None
                          | Some (instrument_id_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (side_value, bytes) =>
                                  Some ({| client_order_id := client_order_id_value; correlation_id := correlation_id_value; last_processed_fill_id := last_processed_fill_id_value; limit_price := limit_price_value; quantity := quantity_value; instrument_id := instrument_id_value; side := side_value |}, bytes)
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
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End StreamOrderMessage.

  Module OrderRejectMessage.

    (** OrderRejectMessage *)
    Record t := {
      timestamp : N;
      client_order_id : N;
      correlation_id : N;
      order_id_optional : N;
      order_reject_reason : N;
      order_reject_details : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (order_reject_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (order_reject_details record) = 47.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (order_id_optional record) ++
      encode_uint 1 (order_reject_reason record) ++
      encode_bytes 47 (order_reject_details record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (client_order_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (correlation_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (order_id_optional_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (order_reject_reason_value, bytes) =>
                          match decode_bytes 47 bytes with
                          | None => None
                          | Some (order_reject_details_value, bytes) =>
                              Some ({| timestamp := timestamp_value; client_order_id := client_order_id_value; correlation_id := correlation_id_value; order_id_optional := order_id_optional_value; order_reject_reason := order_reject_reason_value; order_reject_details := order_reject_details_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 80.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderRejectMessage.

  Module OrderReplacedMessage.

    (** OrderReplacedMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      client_order_id : N;
      correlation_id : N;
      order_id : N;
      receive_time : N;
      total_filled : N;
      available_qty : N;
      instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (receive_time record < 256 ^ N.of_nat 8)%N /\
      (total_filled record < 256 ^ N.of_nat 4)%N /\
      (available_qty record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (receive_time record) ++
      encode_uint_le 4 (total_filled record) ++
      encode_uint_le 4 (available_qty record) ++
      encode_uint_le 4 (instrument_id record).

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
                          | Some (receive_time_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (total_filled_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (available_qty_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (instrument_id_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; exec_id := exec_id_value; client_order_id := client_order_id_value; correlation_id := correlation_id_value; order_id := order_id_value; receive_time := receive_time_value; total_filled := total_filled_value; available_qty := available_qty_value; instrument_id := instrument_id_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length. reflexivity.
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
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderReplacedMessage.

  Module CancelOrderMessage.

    (** CancelOrderMessage *)
    Record t := {
      client_order_id : N;
      correlation_id : N;
      instrument_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 4 (instrument_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (client_order_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  Some ({| client_order_id := client_order_id_value; correlation_id := correlation_id_value; instrument_id := instrument_id_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End CancelOrderMessage.

  Module OrderCanceledMessage.

    (** OrderCanceledMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      client_order_id : N;
      correlation_id : N;
      order_id : N;
      receive_time : N;
      total_filled : N;
      instrument_id : N;
      cancel_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (receive_time record < 256 ^ N.of_nat 8)%N /\
      (total_filled record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (cancel_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (receive_time record) ++
      encode_uint_le 4 (total_filled record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (cancel_reason record).

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
                          | Some (receive_time_value, bytes) =>
                              match decode_uint_le 4 bytes with
                              | None => None
                              | Some (total_filled_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (instrument_id_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (cancel_reason_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; exec_id := exec_id_value; client_order_id := client_order_id_value; correlation_id := correlation_id_value; order_id := order_id_value; receive_time := receive_time_value; total_filled := total_filled_value; instrument_id := instrument_id_value; cancel_reason := cancel_reason_value |}, bytes)
                                      end
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
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderCanceledMessage.

  Module CancelOrderRejectMessage.

    (** CancelOrderRejectMessage *)
    Record t := {
      timestamp : N;
      client_order_id : N;
      correlation_id : N;
      order_id_optional : N;
      cancel_order_reject_reason : N;
      cancel_order_reject_details : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (order_id_optional record < 256 ^ N.of_nat 8)%N /\
      (cancel_order_reject_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (cancel_order_reject_details record) = 31.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (order_id_optional record) ++
      encode_uint 1 (cancel_order_reject_reason record) ++
      encode_bytes 31 (cancel_order_reject_details record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (client_order_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (correlation_id_value, bytes) =>
                  match decode_uint_le 8 bytes with
                  | None => None
                  | Some (order_id_optional_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (cancel_order_reject_reason_value, bytes) =>
                          match decode_bytes 31 bytes with
                          | None => None
                          | Some (cancel_order_reject_details_value, bytes) =>
                              Some ({| timestamp := timestamp_value; client_order_id := client_order_id_value; correlation_id := correlation_id_value; order_id_optional := order_id_optional_value; cancel_order_reject_reason := cancel_order_reject_reason_value; cancel_order_reject_details := cancel_order_reject_details_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelOrderRejectMessage.

  Module MassCancelOrderMessage.

    (** MassCancelOrderMessage *)
    Record t := {
      correlation_id : N;
      limit_price : N;
      instrument_id : N;
      side : N;
      current_session_only : N;
      request_trading_lock : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (limit_price record < 256 ^ N.of_nat 8)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (current_session_only record < 256 ^ N.of_nat 1)%N /\
      (request_trading_lock record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (limit_price record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (current_session_only record) ++
      encode_uint 1 (request_trading_lock record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (limit_price_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (instrument_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (side_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (current_session_only_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (request_trading_lock_value, bytes) =>
                              Some ({| correlation_id := correlation_id_value; limit_price := limit_price_value; instrument_id := instrument_id_value; side := side_value; current_session_only := current_session_only_value; request_trading_lock := request_trading_lock_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MassCancelOrderMessage.

  Module MassCancelOrderAckMessage.

    (** MassCancelOrderAckMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      correlation_id : N;
      canceled_count : N;
      only_current_session : N;
      trading_lock_applied : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (canceled_count record < 256 ^ N.of_nat 4)%N /\
      (only_current_session record < 256 ^ N.of_nat 1)%N /\
      (trading_lock_applied record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 4 (canceled_count record) ++
      encode_uint 1 (only_current_session record) ++
      encode_uint 1 (trading_lock_applied record).

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
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (canceled_count_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (only_current_session_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (trading_lock_applied_value, bytes) =>
                              Some ({| timestamp := timestamp_value; exec_id := exec_id_value; correlation_id := correlation_id_value; canceled_count := canceled_count_value; only_current_session := only_current_session_value; trading_lock_applied := trading_lock_applied_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MassCancelOrderAckMessage.

  Module MassCancelOrderRejectMessage.

    (** MassCancelOrderRejectMessage *)
    Record t := {
      timestamp : N;
      correlation_id : N;
      error_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (error_message record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_bytes 32 (error_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (error_message_value, bytes) =>
                  Some ({| timestamp := timestamp_value; correlation_id := correlation_id_value; error_message := error_message_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MassCancelOrderRejectMessage.

  Module UnlockTradingMessage.

    (** UnlockTradingMessage *)
    Record t := {
      correlation_id : N;
      current_session_only : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (current_session_only record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint 1 (current_session_only record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (current_session_only_value, bytes) =>
              Some ({| correlation_id := correlation_id_value; current_session_only := current_session_only_value |}, bytes)
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

  End UnlockTradingMessage.

  Module UnlockTradingAckMessage.

    (** UnlockTradingAckMessage *)
    Record t := {
      timestamp : N;
      correlation_id : N;
      num_users_affected : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (num_users_affected record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 4 (num_users_affected record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (num_users_affected_value, bytes) =>
                  Some ({| timestamp := timestamp_value; correlation_id := correlation_id_value; num_users_affected := num_users_affected_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End UnlockTradingAckMessage.

  Module UnlockTradingRejectMessage.

    (** UnlockTradingRejectMessage *)
    Record t := {
      timestamp : N;
      correlation_id : N;
      error_message : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (error_message record) = 32.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_bytes 32 (error_message record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (correlation_id_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (error_message_value, bytes) =>
                  Some ({| timestamp := timestamp_value; correlation_id := correlation_id_value; error_message := error_message_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End UnlockTradingRejectMessage.

  Module OrderFilledMessage.

    (** OrderFilledMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      match_id : N;
      client_order_id : N;
      correlation_id : N;
      order_id : N;
      filled_vwap : N;
      total_filled : N;
      available_qty : N;
      fill_price : N;
      fill_qty : N;
      instrument_id : N;
      is_aggressor : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (filled_vwap record < 256 ^ N.of_nat 8)%N /\
      (total_filled record < 256 ^ N.of_nat 4)%N /\
      (available_qty record < 256 ^ N.of_nat 4)%N /\
      (fill_price record < 256 ^ N.of_nat 8)%N /\
      (fill_qty record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (is_aggressor record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (match_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (filled_vwap record) ++
      encode_uint_le 4 (total_filled record) ++
      encode_uint_le 4 (available_qty record) ++
      encode_uint_le 8 (fill_price record) ++
      encode_uint_le 4 (fill_qty record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (is_aggressor record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (match_id_value, bytes) =>
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
                              | Some (filled_vwap_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (total_filled_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (available_qty_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (fill_price_value, bytes) =>
                                              match decode_uint_le 4 bytes with
                                              | None => None
                                              | Some (fill_qty_value, bytes) =>
                                                  match decode_uint_le 4 bytes with
                                                  | None => None
                                                  | Some (instrument_id_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (is_aggressor_value, bytes) =>
                                                          Some ({| timestamp := timestamp_value; exec_id := exec_id_value; match_id := match_id_value; client_order_id := client_order_id_value; correlation_id := correlation_id_value; order_id := order_id_value; filled_vwap := filled_vwap_value; total_filled := total_filled_value; available_qty := available_qty_value; fill_price := fill_price_value; fill_qty := fill_qty_value; instrument_id := instrument_id_value; is_aggressor := is_aggressor_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 81.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderFilledMessage.

  Module SpreadOrderFilledMessage.

    (** SpreadOrderFilledMessage *)
    Record t := {
      timestamp : N;
      exec_id : N;
      match_id : N;
      client_order_id : N;
      correlation_id : N;
      order_id : N;
      filled_vwap : N;
      total_filled : N;
      available_qty : N;
      fill_price : N;
      leg_1_fill_price : N;
      leg_2_fill_price : N;
      fill_qty : N;
      instrument_id : N;
      is_aggressor : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N /\
      (match_id record < 256 ^ N.of_nat 8)%N /\
      (client_order_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (filled_vwap record < 256 ^ N.of_nat 8)%N /\
      (total_filled record < 256 ^ N.of_nat 4)%N /\
      (available_qty record < 256 ^ N.of_nat 4)%N /\
      (fill_price record < 256 ^ N.of_nat 8)%N /\
      (leg_1_fill_price record < 256 ^ N.of_nat 8)%N /\
      (leg_2_fill_price record < 256 ^ N.of_nat 8)%N /\
      (fill_qty record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 4)%N /\
      (is_aggressor record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (exec_id record) ++
      encode_uint_le 8 (match_id record) ++
      encode_uint_le 8 (client_order_id record) ++
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (order_id record) ++
      encode_uint_le 8 (filled_vwap record) ++
      encode_uint_le 4 (total_filled record) ++
      encode_uint_le 4 (available_qty record) ++
      encode_uint_le 8 (fill_price record) ++
      encode_uint_le 8 (leg_1_fill_price record) ++
      encode_uint_le 8 (leg_2_fill_price record) ++
      encode_uint_le 4 (fill_qty record) ++
      encode_uint_le 4 (instrument_id record) ++
      encode_uint 1 (is_aggressor record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (match_id_value, bytes) =>
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
                              | Some (filled_vwap_value, bytes) =>
                                  match decode_uint_le 4 bytes with
                                  | None => None
                                  | Some (total_filled_value, bytes) =>
                                      match decode_uint_le 4 bytes with
                                      | None => None
                                      | Some (available_qty_value, bytes) =>
                                          match decode_uint_le 8 bytes with
                                          | None => None
                                          | Some (fill_price_value, bytes) =>
                                              match decode_uint_le 8 bytes with
                                              | None => None
                                              | Some (leg_1_fill_price_value, bytes) =>
                                                  match decode_uint_le 8 bytes with
                                                  | None => None
                                                  | Some (leg_2_fill_price_value, bytes) =>
                                                      match decode_uint_le 4 bytes with
                                                      | None => None
                                                      | Some (fill_qty_value, bytes) =>
                                                          match decode_uint_le 4 bytes with
                                                          | None => None
                                                          | Some (instrument_id_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (is_aggressor_value, bytes) =>
                                                                  Some ({| timestamp := timestamp_value; exec_id := exec_id_value; match_id := match_id_value; client_order_id := client_order_id_value; correlation_id := correlation_id_value; order_id := order_id_value; filled_vwap := filled_vwap_value; total_filled := total_filled_value; available_qty := available_qty_value; fill_price := fill_price_value; leg_1_fill_price := leg_1_fill_price_value; leg_2_fill_price := leg_2_fill_price_value; fill_qty := fill_qty_value; instrument_id := instrument_id_value; is_aggressor := is_aggressor_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 97.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 bound_14]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint_le by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      rewrite decode_encode_uint_le by exact bound_5.
      rewrite decode_encode_uint_le by exact bound_6.
      rewrite decode_encode_uint_le by exact bound_7.
      rewrite decode_encode_uint_le by exact bound_8.
      rewrite decode_encode_uint_le by exact bound_9.
      rewrite decode_encode_uint_le by exact bound_10.
      rewrite decode_encode_uint_le by exact bound_11.
      rewrite decode_encode_uint_le by exact bound_12.
      rewrite decode_encode_uint_le by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SpreadOrderFilledMessage.

  Module LastExecIdRequestMessage.

    (** LastExecIdRequestMessage *)
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

  End LastExecIdRequestMessage.

  Module LastExecIdMessage.

    (** LastExecIdMessage *)
    Record t := {
      timestamp : N;
      last_exec_id : N;
      correlation_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (last_exec_id record < 256 ^ N.of_nat 8)%N /\
      (correlation_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 8 (last_exec_id record) ++
      encode_uint_le 8 (correlation_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (last_exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (correlation_id_value, bytes) =>
                  Some ({| timestamp := timestamp_value; last_exec_id := last_exec_id_value; correlation_id := correlation_id_value |}, bytes)
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

  End LastExecIdMessage.

  Module EventResendRequestMessage.

    (** EventResendRequestMessage *)
    Record t := {
      correlation_id : N;
      begin_exec_id : N;
      end_exec_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (begin_exec_id record < 256 ^ N.of_nat 8)%N /\
      (end_exec_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 8 (begin_exec_id record) ++
      encode_uint_le 8 (end_exec_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint_le 8 bytes with
          | None => None
          | Some (begin_exec_id_value, bytes) =>
              match decode_uint_le 8 bytes with
              | None => None
              | Some (end_exec_id_value, bytes) =>
                  Some ({| correlation_id := correlation_id_value; begin_exec_id := begin_exec_id_value; end_exec_id := end_exec_id_value |}, bytes)
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

  End EventResendRequestMessage.

  Module EventResendCompleteMessage.

    (** EventResendCompleteMessage *)
    Record t := {
      correlation_id : N;
      resent_event_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (resent_event_count record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint_le 4 (resent_event_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (resent_event_count_value, bytes) =>
              Some ({| correlation_id := correlation_id_value; resent_event_count := resent_event_count_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End EventResendCompleteMessage.

  Module EventResendRejectMessage.

    (** EventResendRejectMessage *)
    Record t := {
      correlation_id : N;
      resend_reject_reason : N;
      event_resend_reject_details : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (correlation_id record < 256 ^ N.of_nat 8)%N /\
      (resend_reject_reason record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (event_resend_reject_details record) = 23.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (correlation_id record) ++
      encode_uint 1 (resend_reject_reason record) ++
      encode_bytes 23 (event_resend_reject_details record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (correlation_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (resend_reject_reason_value, bytes) =>
              match decode_bytes 23 bytes with
              | None => None
              | Some (event_resend_reject_details_value, bytes) =>
                  Some ({| correlation_id := correlation_id_value; resend_reject_reason := resend_reject_reason_value; event_resend_reject_details := event_resend_reject_details_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End EventResendRejectMessage.

End CoinbaseDerivativesOrdersApiV13.
