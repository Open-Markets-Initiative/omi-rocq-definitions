From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Aquis Exchange Aquis Market Data Snapshot

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
  *)

Module AquisEquitiesSnapshotV40.

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

    (** Published as the first message in a snapshot, identifying the continuous stream sequence number and number of securities being reported. *)
    Record t := {
      stream_seq_no : N;
      security_count : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (stream_seq_no record < 256 ^ N.of_nat 4)%N /\
      (security_count record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (stream_seq_no record) ++
      encode_uint 2 (security_count record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (stream_seq_no_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (security_count_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  Some ({| stream_seq_no := stream_seq_no_value; security_count := security_count_value; timestamp := timestamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

    (** Published after each Book Status message to provide details of each order for building the book. *)
    Record t := {
      security_id : N;
      side : N;
      quantity : N;
      price : N;
      order_ref : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_ref record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_ref record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_ref_value, bytes) =>
                          Some ({| security_id := security_id_value; side := side_value; quantity := quantity_value; price := price_value; order_ref := order_ref_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  Module MaCBookEntryMessage.

    (** Published during MaC phase to provide the volume of the 5 best bid and offer orders per security in chronological order. *)
    Record t := {
      security_id : N;
      side : N;
      quantity : N;
      price : N;
      order_ref : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (order_ref record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (order_ref record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (order_ref_value, bytes) =>
                          Some ({| security_id := security_id_value; side := side_value; quantity := quantity_value; price := price_value; order_ref := order_ref_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  End MaCBookEntryMessage.

End AquisEquitiesSnapshotV40.
