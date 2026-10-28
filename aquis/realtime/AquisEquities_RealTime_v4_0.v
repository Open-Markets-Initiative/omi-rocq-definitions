From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Aquis Exchange Real Time Market Data Feed

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

Module AquisEquitiesRealTimeV40.

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

  Module TickTableDataMessage.

    (** Published pre-market to specify dynamic tick tables and static ticks controlling valid price increments for securities on the order book. *)
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

  Module AoDUpdateMessage.

    (** Published during AoD to provide the indicative price and matched volume. *)
    Record t := {
      security_id : N;
      indicative_price : N;
      match_vol : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (match_vol record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 4 (match_vol record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (indicative_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (match_vol_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (timestamp_value, bytes) =>
                      Some ({| security_id := security_id_value; indicative_price := indicative_price_value; match_vol := match_vol_value; timestamp := timestamp_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AoDUpdateMessage.

  Module MaCUpdateMessage.

    (** During the MaC this message is used to publish the indicative price from the buy and sell order totals. *)
    Record t := {
      security_id : N;
      indicative_price : N;
      closing_buy_qty : N;
      closing_sell_qty : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (security_id record < 256 ^ N.of_nat 2)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (closing_buy_qty record < 256 ^ N.of_nat 4)%N /\
      (closing_sell_qty record < 256 ^ N.of_nat 4)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (security_id record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 4 (closing_buy_qty record) ++
      encode_uint 4 (closing_sell_qty record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (security_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (indicative_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (closing_buy_qty_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (closing_sell_qty_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (timestamp_value, bytes) =>
                          Some ({| security_id := security_id_value; indicative_price := indicative_price_value; closing_buy_qty := closing_buy_qty_value; closing_sell_qty := closing_sell_qty_value; timestamp := timestamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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

  End MaCUpdateMessage.

End AquisEquitiesRealTimeV40.
