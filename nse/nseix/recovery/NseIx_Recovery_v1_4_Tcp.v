From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Stock Exchange of India Ltd Mtbt Tick Data Recovery

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

    License: MIT No Attribution
  *)

Module NseIxRecoveryV14Tcp.

  Module StreamHeader.

    (** STREAM_HEADER *)
    Record t := {
      message_length : N;
      stream_id : N;
      sequence_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      (stream_id record < 256 ^ N.of_nat 2)%N /\
      (sequence_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 2 (message_length record) ++
      encode_uint_le 2 (stream_id record) ++
      encode_uint_le 4 (sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint_le 2 bytes with
          | None => None
          | Some (stream_id_value, bytes) =>
              match decode_uint_le 4 bytes with
              | None => None
              | Some (sequence_number_value, bytes) =>
                  Some ({| message_length := message_length_value; stream_id := stream_id_value; sequence_number := sequence_number_value |}, bytes)
              end
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

  End StreamHeader.

  Module MarketStatusMessage.

    (** Sent whenever the status of the market is changed to preopen, preopen-end, open, closed, preclose and preclose-end, for both T and T+1 sessions (section 6.5). *)
    Record t := {
      timestamp : N;
      instrument : list byte;
      status : N;
      session_indc : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (instrument record) = 6 /\
      (status record < 256 ^ N.of_nat 2)%N /\
      (session_indc record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_bytes 6 (instrument record) ++
      encode_uint_le 2 (status record) ++
      encode_uint_le 2 (session_indc record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (instrument_value, bytes) =>
              match decode_uint_le 2 bytes with
              | None => None
              | Some (status_value, bytes) =>
                  match decode_uint_le 2 bytes with
                  | None => None
                  | Some (session_indc_value, bytes) =>
                      Some ({| timestamp := timestamp_value; instrument := instrument_value; status := status_value; session_indc := session_indc_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint_le by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint_le by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStatusMessage.

  Module IndicativePriceAndQuantityMessage.

    (** Indicative equilibrium price and quantity, sent for contracts with pre-open and pre-close sessions, only between the preopen or preclose and the preopen end or preclose end statuses, when the indicative price and quantity are determined or updated during order collection (section 6.6). *)
    Record t := {
      timestamp : N;
      token : N;
      identifier : list byte;
      indicative_price : N;
      indicative_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (token record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (identifier record) = 1 /\
      (indicative_price record < 256 ^ N.of_nat 4)%N /\
      (indicative_quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 8 (timestamp record) ++
      encode_uint_le 4 (token record) ++
      encode_bytes 1 (identifier record) ++
      encode_uint_le 4 (indicative_price record) ++
      encode_uint_le 4 (indicative_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint_le 4 bytes with
          | None => None
          | Some (token_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (identifier_value, bytes) =>
                  match decode_uint_le 4 bytes with
                  | None => None
                  | Some (indicative_price_value, bytes) =>
                      match decode_uint_le 4 bytes with
                      | None => None
                      | Some (indicative_quantity_value, bytes) =>
                          Some ({| timestamp := timestamp_value; token := token_value; identifier := identifier_value; indicative_price := indicative_price_value; indicative_quantity := indicative_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_le_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint_le by exact bound_3.
      rewrite decode_encode_uint_le by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndicativePriceAndQuantityMessage.

  Module HeartbeatMessage.

    (** Sent when there is no data available for a few seconds; the sequence number field in the Stream Header will have the value 0 (zero) (section 9). *)
    Record t := {
      last_sequence_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_sequence_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint_le 4 (last_sequence_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint_le 4 bytes with
      | None => None
      | Some (last_sequence_no_value, bytes) =>
          Some ({| last_sequence_no := last_sequence_no_value |}, bytes)
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

  End HeartbeatMessage.

  Module TickDataRecoveryResponseMessage.

    (** First message sent by the Recovery Server, indicating whether the request was processed successfully; the Stream Header's sequence number is zero. *)
    Record t := {
      request_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (request_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (request_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (request_status_value, bytes) =>
          Some ({| request_status := request_status_value |}, bytes)
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

  End TickDataRecoveryResponseMessage.

End NseIxRecoveryV14Tcp.
