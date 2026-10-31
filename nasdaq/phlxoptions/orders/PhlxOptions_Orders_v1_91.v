From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) PHLX Orders

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
      - the dispatch that chooses a message by its type
      - a run counted by a field
      - a field read in bits
  *)

Module PhlxOptionsOrdersV191.

  Module PacketHeader.

    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 4)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 4 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (message_type_value, bytes) =>
          Some ({| message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module Timestamp.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp.

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. *)
    Record t := {
      timestamp : Timestamp.t;
      event_code : list byte;
      version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Timestamp.bounded (timestamp record) /\
      Datatypes.length (event_code record) = 1 /\
      (version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      Timestamp.encode (timestamp record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 1 (version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Timestamp.decode bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (version_value, bytes) =>
                  Some ({| timestamp := timestamp_value; event_code := event_code_value; version := version_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Timestamp.encode_length, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Timestamp.decode_encode by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp.eq_dec]. Defined.

  End SystemEventMessage.

  Module Timestamp2.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp2.

  Module Timestamp3.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp3.

  Module Timestamp4.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp4.

  Module Timestamp5.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp5.

  Module ComplexTradingActionMessage.

    (** PHLX uses this administrative message to indicate the current trading status of a strategy within the PHLX Options Market. *)
    Record t := {
      timestamp : Timestamp5.t;
      strategy_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Timestamp5.bounded (timestamp record) /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      Timestamp5.encode (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Timestamp5.decode bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (current_trading_state_value, bytes) =>
                  Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; current_trading_state := current_trading_state_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Timestamp5.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Timestamp5.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp5.eq_dec]. Defined.

  End ComplexTradingActionMessage.

  Module Timestamp6.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp6.

  Module Timestamp7.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp7.

  Module StrategyOpenClosedMessage.

    (** PHLX uses this administrative message to indicate when a strategy has completed the opening process or when the strategy has closed and is no longer available for auto execution. *)
    Record t := {
      timestamp : Timestamp7.t;
      strategy_id : N;
      open_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Timestamp7.bounded (timestamp record) /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_state record) = 1.

    Definition encode (record : t) : list byte :=
      Timestamp7.encode (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (open_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Timestamp7.decode bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_state_value, bytes) =>
                  Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; open_state := open_state_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Timestamp7.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Timestamp7.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp7.eq_dec]. Defined.

  End StrategyOpenClosedMessage.

  Module Timestamp8.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp8.

  Module Timestamp9.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp9.

  Module Timestamp10.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp10.

  Module Timestamp11.

    (** Time the message was sent: seconds after midnight and the nanosecond portion, U.S. Eastern Time *)
    Record t := {
      seconds : N;
      nanoseconds : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (seconds record < 256 ^ N.of_nat 4)%N /\
      (nanoseconds record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (seconds record) ++
      encode_uint 4 (nanoseconds record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (seconds_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (nanoseconds_value, bytes) =>
              Some ({| seconds := seconds_value; nanoseconds := nanoseconds_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End Timestamp11.

  Module ComplexAuctionNotificationMessage.

    (** When a Complex Order Live Auction (COLA) or PIXL/Solicitation auction starts for a strategy of an underlying, a COLA/PIXL/Solicitation notification message containing the auction information will be sent. *)
    Record t := {
      timestamp : Timestamp11.t;
      strategy_id : N;
      auction_id : N;
      auction_type : list byte;
      price : N;
      auction_side : list byte;
      debit_or_credit : list byte;
      volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Timestamp11.bounded (timestamp record) /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_type record) = 1 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (auction_side record) = 1 /\
      Datatypes.length (debit_or_credit record) = 1 /\
      (volume record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      Timestamp11.encode (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 4 (auction_id record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (price record) ++
      encode_bytes 1 (auction_side record) ++
      encode_bytes 1 (debit_or_credit record) ++
      encode_uint 4 (volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match Timestamp11.decode bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (auction_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (auction_type_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (auction_side_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (debit_or_credit_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; auction_id := auction_id_value; auction_type := auction_type_value; price := price_value; auction_side := auction_side_value; debit_or_credit := debit_or_credit_value; volume := volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !Timestamp11.encode_length, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite Timestamp11.decode_encode by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec) | apply Timestamp11.eq_dec]. Defined.

  End ComplexAuctionNotificationMessage.

End PhlxOptionsOrdersV191.
