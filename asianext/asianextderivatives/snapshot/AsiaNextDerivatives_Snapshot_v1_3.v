From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * AsiaNext Market Data Snapshot

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
      - a run counted by a field
      - a field read in bits

    License: MIT No Attribution
  *)

Module AsiaNextDerivativesSnapshotV13.

  Module PacketHeader.

    (** Aquis udp packet header *)
    Record t := {
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_count record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_count_value, bytes) =>
          Some ({| message_count := message_count_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End PacketHeader.

  Module MessageHeader.

    (** Aquis market data message header *)
    Record t := {
      msg_type : N;
      msg_length : N;
      seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_type record < 256 ^ N.of_nat 1)%N /\
      (msg_length record < 256 ^ N.of_nat 1)%N /\
      (seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (msg_type record) ++
      encode_uint 1 (msg_length record) ++
      encode_uint 4 (seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (msg_type_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_length_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (seq_no_value, bytes) =>
                  Some ({| msg_type := msg_type_value; msg_length := msg_length_value; seq_no := seq_no_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 6.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End MessageHeader.

  Module SnapshotStartMessage.

    (** A Snapshot Start message is published as the first message in a snapshot to identify the sequence number in the continuous stream that this snapshot relates to. *)
    Record t := {
      stream_seq_no : N;
      security_count : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stream_seq_no record < 256 ^ N.of_nat 4)%N /\
      (security_count record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (stream_seq_no record) ++
      encode_uint 4 (security_count record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (stream_seq_no_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (security_count_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  Some ({| stream_seq_no := stream_seq_no_value; security_count := security_count_value; timestamp := timestamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SnapshotStartMessage.

  Module BookEntryMessage.

    (** An appropriate number of Book Entry messages is published after each Book Status message to provide details of each order and allow the book to be built. *)
    Record t := {
      security_id : N;
      side : N;
      quantity : N;
      price : N;
      order_ref : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 4)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_ref record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (security_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (order_ref record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_ref_value, bytes) =>
                          Some ({| security_id := security_id_value; side := side_value; quantity := quantity_value; price := price_value; order_ref := order_ref_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 29.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End BookEntryMessage.

  Module TickTableDataMessage.

    (** A series of Tick Table Data messages are published to specify the dynamic tick tables and static ticks that apply to the securities traded on AsiaNext. *)
    Record t := {
      tick_table_id : N;
      name : list byte;
      threshold : N;
      tick_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tick_table_id record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (name record) = 10 /\
      (threshold record < 256 ^ N.of_nat 8)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (tick_table_id record) ++
      encode_bytes 10 (name record) ++
      encode_uint 8 (threshold record) ++
      encode_uint 8 (tick_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (tick_table_id_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (name_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (threshold_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (tick_size_value, bytes) =>
                      Some ({| tick_table_id := tick_table_id_value; name := name_value; threshold := threshold_value; tick_size := tick_size_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 27.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TickTableDataMessage.

  Module LotSizeComposite.

    (** Lot size scaled at runtime by lotSizeDecimal *)
    Record t := {
      lot_size : N;
      lot_size_decimal : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (lot_size record < 256 ^ N.of_nat 8)%N /\
      (lot_size_decimal record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (lot_size record) ++
      encode_uint 1 (lot_size_decimal record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (lot_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (lot_size_decimal_value, bytes) =>
              Some ({| lot_size := lot_size_value; lot_size_decimal := lot_size_decimal_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End LotSizeComposite.

  Module ContractSizeComposite.

    (** Contract size scaled at runtime by contractSizeDecimals *)
    Record t := {
      contract_size : N;
      contract_size_decimals : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (contract_size record < 256 ^ N.of_nat 8)%N /\
      (contract_size_decimals record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (contract_size record) ++
      encode_uint 1 (contract_size_decimals record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (contract_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (contract_size_decimals_value, bytes) =>
              Some ({| contract_size := contract_size_value; contract_size_decimals := contract_size_decimals_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
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

  End ContractSizeComposite.

  Module SequenceNumberResetMessage.

    (** The Sequence Number Reset is published when AsiaNext initiates a seqNo reset. *)
    Record t := {
      next_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (next_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (next_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (next_seq_no_value, bytes) =>
          Some ({| next_seq_no := next_seq_no_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
    Proof.
      intros record. unfold encode.
      rewrite !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_uint by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SequenceNumberResetMessage.

End AsiaNextDerivativesSnapshotV13.
