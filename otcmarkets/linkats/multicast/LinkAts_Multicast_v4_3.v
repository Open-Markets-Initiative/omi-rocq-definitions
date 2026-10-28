From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * OTC Markets Group OTC Markets Multicast

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
      - a Composite rule
      - a run counted by a field
      - a field read in bits
  *)

Module LinkAtsMulticastV43.

  Module MessageHeader.

    (** Otc Udp Message Header *)
    Record t := {
      message_size : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_size record < 256 ^ N.of_nat 2)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_size record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_size := message_size_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End MessageHeader.

  Module StartOfSpinMessage.

    (** This message appears on all quote channels and indicates the beginning of a spin message cycle. *)
    Record t := {
      channel_seq_num : N;
      spin_type : N;
      spin_start_time_milli : N;
      spin_last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_seq_num record < 256 ^ N.of_nat 4)%N /\
      (spin_type record < 256 ^ N.of_nat 1)%N /\
      (spin_start_time_milli record < 256 ^ N.of_nat 8)%N /\
      (spin_last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (channel_seq_num record) ++
      encode_uint 1 (spin_type record) ++
      encode_uint 8 (spin_start_time_milli record) ++
      encode_uint 4 (spin_last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (channel_seq_num_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (spin_type_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (spin_start_time_milli_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (spin_last_seq_num_value, bytes) =>
                      Some ({| channel_seq_num := channel_seq_num_value; spin_type := spin_type_value; spin_start_time_milli := spin_start_time_milli_value; spin_last_seq_num := spin_last_seq_num_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End StartOfSpinMessage.

  Module EndOfSpinMessage.

    (** This message appears on all quote channels and indicates the end of a spin message cycle. *)
    Record t := {
      channel_seq_num : N;
      spin_type : N;
      spin_msg_ct : N;
      spin_end_time_milli : N;
      spin_last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_seq_num record < 256 ^ N.of_nat 4)%N /\
      (spin_type record < 256 ^ N.of_nat 1)%N /\
      (spin_msg_ct record < 256 ^ N.of_nat 4)%N /\
      (spin_end_time_milli record < 256 ^ N.of_nat 8)%N /\
      (spin_last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (channel_seq_num record) ++
      encode_uint 1 (spin_type record) ++
      encode_uint 4 (spin_msg_ct record) ++
      encode_uint 8 (spin_end_time_milli record) ++
      encode_uint 4 (spin_last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (channel_seq_num_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (spin_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (spin_msg_ct_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (spin_end_time_milli_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (spin_last_seq_num_value, bytes) =>
                          Some ({| channel_seq_num := channel_seq_num_value; spin_type := spin_type_value; spin_msg_ct := spin_msg_ct_value; spin_end_time_milli := spin_end_time_milli_value; spin_last_seq_num := spin_last_seq_num_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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

  End EndOfSpinMessage.

  Module MarketOpenMessage.

    (** This message is sent out at 6 AM on all channels. The message can also be sent mid-day if a technical outage caused a temporary closure of the market. *)
    Record t := {
      channel_seq_num : N;
      market_open : N;
      market_close : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_seq_num record < 256 ^ N.of_nat 4)%N /\
      (market_open record < 256 ^ N.of_nat 8)%N /\
      (market_close record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (channel_seq_num record) ++
      encode_uint 8 (market_open record) ++
      encode_uint 8 (market_close record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (channel_seq_num_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (market_open_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (market_close_value, bytes) =>
                  Some ({| channel_seq_num := channel_seq_num_value; market_open := market_open_value; market_close := market_close_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End MarketOpenMessage.

  Module MarketCloseMessage.

    (** This message is sent out at 5 PM on all channels. The message can also be sent mid-day if a technical outage causes a temporary closure of the market. *)
    Record t := {
      channel_seq_num : N;
      market_close_time_milli : N;
      market_msg_ct : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_seq_num record < 256 ^ N.of_nat 4)%N /\
      (market_close_time_milli record < 256 ^ N.of_nat 8)%N /\
      (market_msg_ct record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (channel_seq_num record) ++
      encode_uint 8 (market_close_time_milli record) ++
      encode_uint 4 (market_msg_ct record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (channel_seq_num_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (market_close_time_milli_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (market_msg_ct_value, bytes) =>
                  Some ({| channel_seq_num := channel_seq_num_value; market_close_time_milli := market_close_time_milli_value; market_msg_ct := market_msg_ct_value |}, bytes)
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

  End MarketCloseMessage.

End LinkAtsMulticastV43.
