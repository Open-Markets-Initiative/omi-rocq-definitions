From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The London Metal Exchange LMEsource Level2 Refresh

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

Module LmeSelectLevel2SnapshotV418.

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

  Module MarketStateContractMessage.

    (** Indicates the trading state of instruments at the contract level, for example Copper Futures or Aluminium Options. The ContractCode field is common across the Market State - Contract, Outright Definition and Strategy Definition messages and links the contract state to individual tradable instruments. *)
    Record t := {
      trading_venue : list byte;
      time_of_event : N;
      contract_code : list byte;
      trading_state : N;
      start_time : N;
      end_time : N;
      trading_state_condition : list byte;
      filler_string_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_venue record) = 2 /\
      (time_of_event record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (contract_code record) = 12 /\
      (trading_state record < 256 ^ N.of_nat 1)%N /\
      (start_time record < 256 ^ N.of_nat 8)%N /\
      (end_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trading_state_condition record) = 1 /\
      Datatypes.length (filler_string_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (trading_venue record) ++
      encode_uint 8 (time_of_event record) ++
      encode_bytes 12 (contract_code record) ++
      encode_uint 1 (trading_state record) ++
      encode_uint 8 (start_time record) ++
      encode_uint 8 (end_time record) ++
      encode_bytes 1 (trading_state_condition record) ++
      encode_bytes 2 (filler_string_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (trading_venue_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (time_of_event_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (contract_code_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (trading_state_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (start_time_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (end_time_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trading_state_condition_value, bytes) =>
                                  match decode_bytes 2 bytes with
                                  | None => None
                                  | Some (filler_string_2_value, bytes) =>
                                      Some ({| trading_venue := trading_venue_value; time_of_event := time_of_event_value; contract_code := contract_code_value; trading_state := trading_state_value; start_time := start_time_value; end_time := end_time_value; trading_state_condition := trading_state_condition_value; filler_string_2 := filler_string_2_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 42.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStateContractMessage.

  Module MarketStateInstrumentMessage.

    (** Indicates the trading state of an individual tradable instrument. Sent when the instrument state differs from that at contract level, for example when TOM goes into Post Trade before the contract. *)
    Record t := {
      trading_venue : list byte;
      time_of_event : N;
      tradable_instrument_id : N;
      timetable_control_type : list byte;
      trading_state : N;
      start_time : N;
      end_time : N;
      trading_state_condition : list byte;
      filler_string_3 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_venue record) = 2 /\
      (time_of_event record < 256 ^ N.of_nat 8)%N /\
      (tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (timetable_control_type record) = 1 /\
      (trading_state record < 256 ^ N.of_nat 1)%N /\
      (start_time record < 256 ^ N.of_nat 8)%N /\
      (end_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trading_state_condition record) = 1 /\
      Datatypes.length (filler_string_3 record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (trading_venue record) ++
      encode_uint 8 (time_of_event record) ++
      encode_uint 8 (tradable_instrument_id record) ++
      encode_bytes 1 (timetable_control_type record) ++
      encode_uint 1 (trading_state record) ++
      encode_uint 8 (start_time record) ++
      encode_uint 8 (end_time record) ++
      encode_bytes 1 (trading_state_condition record) ++
      encode_bytes 3 (filler_string_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (trading_venue_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (time_of_event_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tradable_instrument_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (timetable_control_type_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trading_state_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (start_time_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (end_time_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (trading_state_condition_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (filler_string_3_value, bytes) =>
                                          Some ({| trading_venue := trading_venue_value; time_of_event := time_of_event_value; tradable_instrument_id := tradable_instrument_id_value; timetable_control_type := timetable_control_type_value; trading_state := trading_state_value; start_time := start_time_value; end_time := end_time_value; trading_state_condition := trading_state_condition_value; filler_string_3 := filler_string_3_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStateInstrumentMessage.

  Module IndicativeOpeningPriceMessage.

    (** Carries the price at which a tradable instrument would open, computed by the uncrossing algorithm during Pre-Open. If there are no crossed prices no IOP is calculated or disseminated; where the book is not crossed but has both a bid and an offer, a mid price is calculated and published instead. At the transition from Pre-Open to Open an IOP message is published for every tradable instrument with both prices null and the volume zero, to indicate the prices are no longer valid. *)
    Record t := {
      trading_venue : list byte;
      time_of_event : N;
      tradable_instrument_id : N;
      indicative_opening_price : N;
      indicative_opening_volume : N;
      indicative_opening_mid_price : N;
      filler_string_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_venue record) = 2 /\
      (time_of_event record < 256 ^ N.of_nat 8)%N /\
      (tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      (indicative_opening_price record < 256 ^ N.of_nat 8)%N /\
      (indicative_opening_volume record < 256 ^ N.of_nat 4)%N /\
      (indicative_opening_mid_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (filler_string_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (trading_venue record) ++
      encode_uint 8 (time_of_event record) ++
      encode_uint 8 (tradable_instrument_id record) ++
      encode_uint 8 (indicative_opening_price record) ++
      encode_uint 4 (indicative_opening_volume record) ++
      encode_uint 8 (indicative_opening_mid_price record) ++
      encode_bytes 2 (filler_string_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (trading_venue_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (time_of_event_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tradable_instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (indicative_opening_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (indicative_opening_volume_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (indicative_opening_mid_price_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (filler_string_2_value, bytes) =>
                                  Some ({| trading_venue := trading_venue_value; time_of_event := time_of_event_value; tradable_instrument_id := tradable_instrument_id_value; indicative_opening_price := indicative_opening_price_value; indicative_opening_volume := indicative_opening_volume_value; indicative_opening_mid_price := indicative_opening_mid_price_value; filler_string_2 := filler_string_2_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 40.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndicativeOpeningPriceMessage.

  Module QuoteRequestMessage.

    (** Generated when a request for quote is accepted by the Matching Engine. *)
    Record t := {
      trading_venue : list byte;
      time_of_event : N;
      tradable_instrument_id : N;
      quote_request_type : N;
      buy_sell : list byte;
      volume : N;
      filler_string_2 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_venue record) = 2 /\
      (time_of_event record < 256 ^ N.of_nat 8)%N /\
      (tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      (quote_request_type record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (buy_sell record) = 1 /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (filler_string_2 record) = 2.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (trading_venue record) ++
      encode_uint 8 (time_of_event record) ++
      encode_uint 8 (tradable_instrument_id record) ++
      encode_uint 1 (quote_request_type record) ++
      encode_bytes 1 (buy_sell record) ++
      encode_uint 4 (volume record) ++
      encode_bytes 2 (filler_string_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (trading_venue_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (time_of_event_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tradable_instrument_id_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (quote_request_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (buy_sell_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_bytes 2 bytes with
                              | None => None
                              | Some (filler_string_2_value, bytes) =>
                                  Some ({| trading_venue := trading_venue_value; time_of_event := time_of_event_value; tradable_instrument_id := tradable_instrument_id_value; quote_request_type := quote_request_type_value; buy_sell := buy_sell_value; volume := volume_value; filler_string_2 := filler_string_2_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End QuoteRequestMessage.

  Module RefreshCompleteMessage.

    (** Published to mark the end of a refresh cycle. *)
    Record t := {
      last_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (last_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (last_seq_num_value, bytes) =>
          Some ({| last_seq_num := last_seq_num_value |}, bytes)
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

  End RefreshCompleteMessage.

End LmeSelectLevel2SnapshotV418.
