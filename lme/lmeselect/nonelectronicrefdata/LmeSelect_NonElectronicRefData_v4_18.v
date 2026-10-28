From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The London Metal Exchange LMEsource NonElectronicRefData

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
  *)

Module LmeSelectNonElectronicRefDataV418.

  Module PacketHeader.

    (** LMEsource packet header, giving the packet size, the number of messages it carries, the sequence number of the first of them and the time the packet was sent *)
    Record t := {
      pkt_size : N;
      msg_count : N;
      filler : list byte;
      seq_num : N;
      send_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pkt_size record < 256 ^ N.of_nat 2)%N /\
      (msg_count record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (filler record) = 1 /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (send_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (pkt_size record) ++
      encode_uint 1 (msg_count record) ++
      encode_bytes 1 (filler record) ++
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (send_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (pkt_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_count_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (filler_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (send_time_value, bytes) =>
                          Some ({| pkt_size := pkt_size_value; msg_count := msg_count_value; filler := filler_value; seq_num := seq_num_value; send_time := send_time_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 16.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End PacketHeader.

  Module MessageHeader.

    (** LMEsource message header, giving the size of the message and its type *)
    Record t := {
      msg_size : N;
      msg_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (msg_size record < 256 ^ N.of_nat 2)%N /\
      (msg_type record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (msg_size record) ++
      encode_uint 2 (msg_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (msg_size_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (msg_type_value, bytes) =>
              Some ({| msg_size := msg_size_value; msg_type := msg_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  Module SequenceResetMessage.

    (** Sent on each multicast channel at start of day, and intraday in case of a disaster recovery. The client must ignore the sequence number of the Sequence Reset message itself and set the next expected sequence number to NewSeqNo, clear all cached data for all instruments and subscribe to the refresh channels to receive the current state of the market. *)
    Record t := {
      new_seq_no : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (new_seq_no record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (new_seq_no record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (new_seq_no_value, bytes) =>
          Some ({| new_seq_no := new_seq_no_value |}, bytes)
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

  End SequenceResetMessage.

  Module InstrumentDefinitionMessage.

    (** Describes a futures outright prompt date or option call or put strike. *)
    Record t := {
      instrument_id : N;
      name : list byte;
      contract_code : list byte;
      underlying_instrument_id : N;
      expiry_date : N;
      strike_price : N;
      option_type : list byte;
      cfi_code : list byte;
      isin : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (name record) = 40 /\
      Datatypes.length (contract_code record) = 12 /\
      (underlying_instrument_id record < 256 ^ N.of_nat 8)%N /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (option_type record) = 1 /\
      Datatypes.length (cfi_code record) = 6 /\
      Datatypes.length (isin record) = 12.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (instrument_id record) ++
      encode_bytes 40 (name record) ++
      encode_bytes 12 (contract_code record) ++
      encode_uint 8 (underlying_instrument_id record) ++
      encode_uint 4 (expiry_date record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (option_type record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_bytes 12 (isin record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (instrument_id_value, bytes) =>
          match decode_bytes 40 bytes with
          | None => None
          | Some (name_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (contract_code_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (underlying_instrument_id_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (expiry_date_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (option_type_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (cfi_code_value, bytes) =>
                                      match decode_bytes 12 bytes with
                                      | None => None
                                      | Some (isin_value, bytes) =>
                                          Some ({| instrument_id := instrument_id_value; name := name_value; contract_code := contract_code_value; underlying_instrument_id := underlying_instrument_id_value; expiry_date := expiry_date_value; strike_price := strike_price_value; option_type := option_type_value; cfi_code := cfi_code_value; isin := isin_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 99.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentDefinitionMessage.

  Module OrderStatisticsIntradayMessage.

    (** Generated at the end of each Ring trading session for instruments that have traded. Two messages are published, one for each high price and low price. If no price has been received the field is set to null. *)
    Record t := {
      time_of_event : N;
      tradable_instrument_id : N;
      trading_venue : list byte;
      ring_session : list byte;
      order_high : N;
      order_low : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_of_event record < 256 ^ N.of_nat 8)%N /\
      (tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trading_venue record) = 2 /\
      Datatypes.length (ring_session record) = 2 /\
      (order_high record < 256 ^ N.of_nat 8)%N /\
      (order_low record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_of_event record) ++
      encode_uint 8 (tradable_instrument_id record) ++
      encode_bytes 2 (trading_venue record) ++
      encode_bytes 2 (ring_session record) ++
      encode_uint 8 (order_high record) ++
      encode_uint 8 (order_low record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_of_event_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (tradable_instrument_id_value, bytes) =>
              match decode_bytes 2 bytes with
              | None => None
              | Some (trading_venue_value, bytes) =>
                  match decode_bytes 2 bytes with
                  | None => None
                  | Some (ring_session_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (order_high_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (order_low_value, bytes) =>
                              Some ({| time_of_event := time_of_event_value; tradable_instrument_id := tradable_instrument_id_value; trading_venue := trading_venue_value; ring_session := ring_session_value; order_high := order_high_value; order_low := order_low_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderStatisticsIntradayMessage.

End LmeSelectNonElectronicRefDataV418.
