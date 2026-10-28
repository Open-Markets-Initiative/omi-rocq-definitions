From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The London Metal Exchange LMEsource ReferencePrices

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

Module LmeSelectReferencePricesV418.

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

  Module ReferencePriceMessage.

    (** Reference prices are published for instruments with an InstrumentID for the Official, Settlement, Closing and Index price types. Instruments are published in the Instrument Definition message. *)
    Record t := {
      time_of_event : N;
      reference_price_category : list byte;
      reference_price_type : list byte;
      price_status : list byte;
      business_date : N;
      instrument_id : N;
      product_code : list byte;
      currency_code : list byte;
      bid : N;
      price : N;
      ask : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_of_event record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reference_price_category record) = 1 /\
      Datatypes.length (reference_price_type record) = 32 /\
      Datatypes.length (price_status record) = 12 /\
      (business_date record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (product_code record) = 2 /\
      Datatypes.length (currency_code record) = 3 /\
      (bid record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (ask record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (time_of_event record) ++
      encode_bytes 1 (reference_price_category record) ++
      encode_bytes 32 (reference_price_type record) ++
      encode_bytes 12 (price_status record) ++
      encode_uint 4 (business_date record) ++
      encode_uint 8 (instrument_id record) ++
      encode_bytes 2 (product_code record) ++
      encode_bytes 3 (currency_code record) ++
      encode_uint 8 (bid record) ++
      encode_uint 8 (price record) ++
      encode_uint 8 (ask record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (time_of_event_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (reference_price_category_value, bytes) =>
              match decode_bytes 32 bytes with
              | None => None
              | Some (reference_price_type_value, bytes) =>
                  match decode_bytes 12 bytes with
                  | None => None
                  | Some (price_status_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (business_date_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (instrument_id_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (product_code_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (currency_code_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (bid_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (ask_value, bytes) =>
                                                  Some ({| time_of_event := time_of_event_value; reference_price_category := reference_price_category_value; reference_price_type := reference_price_type_value; price_status := price_status_value; business_date := business_date_value; instrument_id := instrument_id_value; product_code := product_code_value; currency_code := currency_code_value; bid := bid_value; price := price_value; ask := ask_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 94.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 bound_10]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReferencePriceMessage.

  Module ReferenceFxRateMessage.

    (** Exchange FX rates are published for the Cash prompt. Daily and Monthly Moving Average Exchange FX rates are published each day, with the Monthly Average Exchange FX rate published on the last business day of the month. MonthlyMovingAverage and MonthlyAverage are published only for the Exchange category. *)
    Record t := {
      fx_rate_category : list byte;
      fx_rate_type : list byte;
      business_date : N;
      maturity_date : N;
      base_currency_code : list byte;
      target_currency_code : list byte;
      conversion_rate : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (fx_rate_category record) = 1 /\
      Datatypes.length (fx_rate_type record) = 2 /\
      (business_date record < 256 ^ N.of_nat 4)%N /\
      (maturity_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (base_currency_code record) = 3 /\
      Datatypes.length (target_currency_code record) = 3 /\
      (conversion_rate record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (fx_rate_category record) ++
      encode_bytes 2 (fx_rate_type record) ++
      encode_uint 4 (business_date record) ++
      encode_uint 4 (maturity_date record) ++
      encode_bytes 3 (base_currency_code record) ++
      encode_bytes 3 (target_currency_code record) ++
      encode_uint 8 (conversion_rate record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (fx_rate_category_value, bytes) =>
          match decode_bytes 2 bytes with
          | None => None
          | Some (fx_rate_type_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (business_date_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (maturity_date_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (base_currency_code_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (target_currency_code_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (conversion_rate_value, bytes) =>
                                  Some ({| fx_rate_category := fx_rate_category_value; fx_rate_type := fx_rate_type_value; business_date := business_date_value; maturity_date := maturity_date_value; base_currency_code := base_currency_code_value; target_currency_code := target_currency_code_value; conversion_rate := conversion_rate_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ReferenceFxRateMessage.

End LmeSelectReferencePricesV418.
