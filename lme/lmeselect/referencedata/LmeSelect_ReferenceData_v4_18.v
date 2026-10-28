From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * The London Metal Exchange LMEsource ReferenceData

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

Module LmeSelectReferenceDataV418.

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

  Module ContractDefinitionMessage.

    (** Published for a new contract prior to its first trading date, to enable participants to configure risk management parameters before the contract becomes tradable. *)
    Record t := {
      trading_venue : list byte;
      contract_code : list byte;
      name : list byte;
      contract_type : list byte;
      product_code : list byte;
      underlying_type : list byte;
      underlying_contract_code : list byte;
      trading_currency : list byte;
      settlement_type : list byte;
      settlement_pricing_method : list byte;
      exercise_style : N;
      lot_unit : list byte;
      lot_size : N;
      lot_size_type : list byte;
      contract_price_type : list byte;
      first_trading_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_venue record) = 2 /\
      Datatypes.length (contract_code record) = 12 /\
      Datatypes.length (name record) = 64 /\
      Datatypes.length (contract_type record) = 1 /\
      Datatypes.length (product_code record) = 2 /\
      Datatypes.length (underlying_type record) = 1 /\
      Datatypes.length (underlying_contract_code record) = 12 /\
      Datatypes.length (trading_currency record) = 3 /\
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (settlement_pricing_method record) = 1 /\
      (exercise_style record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (lot_unit record) = 20 /\
      (lot_size record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (lot_size_type record) = 1 /\
      Datatypes.length (contract_price_type record) = 1 /\
      (first_trading_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (trading_venue record) ++
      encode_bytes 12 (contract_code record) ++
      encode_bytes 64 (name record) ++
      encode_bytes 1 (contract_type record) ++
      encode_bytes 2 (product_code record) ++
      encode_bytes 1 (underlying_type record) ++
      encode_bytes 12 (underlying_contract_code record) ++
      encode_bytes 3 (trading_currency record) ++
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (settlement_pricing_method record) ++
      encode_uint 1 (exercise_style record) ++
      encode_bytes 20 (lot_unit record) ++
      encode_uint 8 (lot_size record) ++
      encode_bytes 1 (lot_size_type record) ++
      encode_bytes 1 (contract_price_type record) ++
      encode_uint 4 (first_trading_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (trading_venue_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (contract_code_value, bytes) =>
              match decode_bytes 64 bytes with
              | None => None
              | Some (name_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (contract_type_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (product_code_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (underlying_type_value, bytes) =>
                              match decode_bytes 12 bytes with
                              | None => None
                              | Some (underlying_contract_code_value, bytes) =>
                                  match decode_bytes 3 bytes with
                                  | None => None
                                  | Some (trading_currency_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (settlement_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (settlement_pricing_method_value, bytes) =>
                                              match decode_uint 1 bytes with
                                              | None => None
                                              | Some (exercise_style_value, bytes) =>
                                                  match decode_bytes 20 bytes with
                                                  | None => None
                                                  | Some (lot_unit_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (lot_size_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (lot_size_type_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (contract_price_type_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (first_trading_date_value, bytes) =>
                                                                      Some ({| trading_venue := trading_venue_value; contract_code := contract_code_value; name := name_value; contract_type := contract_type_value; product_code := product_code_value; underlying_type := underlying_type_value; underlying_contract_code := underlying_contract_code_value; trading_currency := trading_currency_value; settlement_type := settlement_type_value; settlement_pricing_method := settlement_pricing_method_value; exercise_style := exercise_style_value; lot_unit := lot_unit_value; lot_size := lot_size_value; lot_size_type := lot_size_type_value; contract_price_type := contract_price_type_value; first_trading_date := first_trading_date_value |}, bytes)
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
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 134.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ContractDefinitionMessage.

  Module OutrightDefinitionMessage.

    (** Describes individual outright tradable instruments available from LMEsource. *)
    Record t := {
      trading_venue : list byte;
      tradable_instrument_id : N;
      merged_tradable_instrument_id : N;
      linked_tradable_instrument_id : N;
      product_code : list byte;
      contract_type : list byte;
      trading_currency : list byte;
      contract_code : list byte;
      expiry_date : N;
      prompt_type : list byte;
      strike_price : N;
      option_type : list byte;
      exercise_style : N;
      prompt_date_label : list byte;
      price_code : list byte;
      isin : list byte;
      cfi_code : list byte;
      market_code : list byte;
      market_segment_code : list byte;
      tick_size_id : N;
      lot_size : N;
      lot_size_type : list byte;
      last_trading_date : N;
      settlement_type : list byte;
      settlement_pricing_method : list byte;
      underlying_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_venue record) = 2 /\
      (tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      (merged_tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      (linked_tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (product_code record) = 2 /\
      Datatypes.length (contract_type record) = 1 /\
      Datatypes.length (trading_currency record) = 3 /\
      Datatypes.length (contract_code record) = 12 /\
      (expiry_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (prompt_type record) = 1 /\
      (strike_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (option_type record) = 1 /\
      (exercise_style record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (prompt_date_label record) = 6 /\
      Datatypes.length (price_code record) = 2 /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (cfi_code record) = 6 /\
      Datatypes.length (market_code record) = 4 /\
      Datatypes.length (market_segment_code record) = 12 /\
      (tick_size_id record < 256 ^ N.of_nat 4)%N /\
      (lot_size record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (lot_size_type record) = 1 /\
      (last_trading_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_type record) = 1 /\
      Datatypes.length (settlement_pricing_method record) = 1 /\
      Datatypes.length (underlying_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (trading_venue record) ++
      encode_uint 8 (tradable_instrument_id record) ++
      encode_uint 8 (merged_tradable_instrument_id record) ++
      encode_uint 8 (linked_tradable_instrument_id record) ++
      encode_bytes 2 (product_code record) ++
      encode_bytes 1 (contract_type record) ++
      encode_bytes 3 (trading_currency record) ++
      encode_bytes 12 (contract_code record) ++
      encode_uint 4 (expiry_date record) ++
      encode_bytes 1 (prompt_type record) ++
      encode_uint 8 (strike_price record) ++
      encode_bytes 1 (option_type record) ++
      encode_uint 1 (exercise_style record) ++
      encode_bytes 6 (prompt_date_label record) ++
      encode_bytes 2 (price_code record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 6 (cfi_code record) ++
      encode_bytes 4 (market_code record) ++
      encode_bytes 12 (market_segment_code record) ++
      encode_uint 4 (tick_size_id record) ++
      encode_uint 8 (lot_size record) ++
      encode_bytes 1 (lot_size_type record) ++
      encode_uint 4 (last_trading_date record) ++
      encode_bytes 1 (settlement_type record) ++
      encode_bytes 1 (settlement_pricing_method record) ++
      encode_bytes 1 (underlying_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (trading_venue_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (tradable_instrument_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (merged_tradable_instrument_id_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (linked_tradable_instrument_id_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (product_code_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (contract_type_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (trading_currency_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (contract_code_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (expiry_date_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (prompt_type_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (strike_price_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (option_type_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (exercise_style_value, bytes) =>
                                                          match decode_bytes 6 bytes with
                                                          | None => None
                                                          | Some (prompt_date_label_value, bytes) =>
                                                              match decode_bytes 2 bytes with
                                                              | None => None
                                                              | Some (price_code_value, bytes) =>
                                                                  match decode_bytes 12 bytes with
                                                                  | None => None
                                                                  | Some (isin_value, bytes) =>
                                                                      match decode_bytes 6 bytes with
                                                                      | None => None
                                                                      | Some (cfi_code_value, bytes) =>
                                                                          match decode_bytes 4 bytes with
                                                                          | None => None
                                                                          | Some (market_code_value, bytes) =>
                                                                              match decode_bytes 12 bytes with
                                                                              | None => None
                                                                              | Some (market_segment_code_value, bytes) =>
                                                                                  match decode_uint 4 bytes with
                                                                                  | None => None
                                                                                  | Some (tick_size_id_value, bytes) =>
                                                                                      match decode_uint 8 bytes with
                                                                                      | None => None
                                                                                      | Some (lot_size_value, bytes) =>
                                                                                          match decode_bytes 1 bytes with
                                                                                          | None => None
                                                                                          | Some (lot_size_type_value, bytes) =>
                                                                                              match decode_uint 4 bytes with
                                                                                              | None => None
                                                                                              | Some (last_trading_date_value, bytes) =>
                                                                                                  match decode_bytes 1 bytes with
                                                                                                  | None => None
                                                                                                  | Some (settlement_type_value, bytes) =>
                                                                                                      match decode_bytes 1 bytes with
                                                                                                      | None => None
                                                                                                      | Some (settlement_pricing_method_value, bytes) =>
                                                                                                          match decode_bytes 1 bytes with
                                                                                                          | None => None
                                                                                                          | Some (underlying_type_value, bytes) =>
                                                                                                              Some ({| trading_venue := trading_venue_value; tradable_instrument_id := tradable_instrument_id_value; merged_tradable_instrument_id := merged_tradable_instrument_id_value; linked_tradable_instrument_id := linked_tradable_instrument_id_value; product_code := product_code_value; contract_type := contract_type_value; trading_currency := trading_currency_value; contract_code := contract_code_value; expiry_date := expiry_date_value; prompt_type := prompt_type_value; strike_price := strike_price_value; option_type := option_type_value; exercise_style := exercise_style_value; prompt_date_label := prompt_date_label_value; price_code := price_code_value; isin := isin_value; cfi_code := cfi_code_value; market_code := market_code_value; market_segment_code := market_segment_code_value; tick_size_id := tick_size_id_value; lot_size := lot_size_value; lot_size_type := lot_size_type_value; last_trading_date := last_trading_date_value; settlement_type := settlement_type_value; settlement_pricing_method := settlement_pricing_method_value; underlying_type := underlying_type_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 121.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 [bound_21 [bound_22 [bound_23 [bound_24 bound_25]]]]]]]]]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_bytes by exact bound_21.
      rewrite decode_encode_uint by exact bound_22.
      rewrite decode_encode_bytes by exact bound_23.
      rewrite decode_encode_bytes by exact bound_24.
      rewrite decode_encode_bytes by exact bound_25.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OutrightDefinitionMessage.

  Module PriceLimitsMessage.

    (** Describes the upper and lower price limits for an outright tradable instrument. Where Daily Price Limits are enabled for a contract they are published for electronic tradable instruments, and the same limits also apply to non-electronic tradable instruments. *)
    Record t := {
      tradable_instrument_id : N;
      upper_price_limit : N;
      lower_price_limit : N;
      transaction_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      (upper_price_limit record < 256 ^ N.of_nat 8)%N /\
      (lower_price_limit record < 256 ^ N.of_nat 8)%N /\
      (transaction_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (tradable_instrument_id record) ++
      encode_uint 8 (upper_price_limit record) ++
      encode_uint 8 (lower_price_limit record) ++
      encode_uint 8 (transaction_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (tradable_instrument_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (upper_price_limit_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (lower_price_limit_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (transaction_time_value, bytes) =>
                      Some ({| tradable_instrument_id := tradable_instrument_id_value; upper_price_limit := upper_price_limit_value; lower_price_limit := lower_price_limit_value; transaction_time := transaction_time_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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

  End PriceLimitsMessage.

  Module TradeStatisticsEndOfDayMessage.

    (** Generated when the market moves to the Post-Trade session for instruments that have traded. LMEsource publishes the LMEselect Opening and Closing Prices, LMEselect Trading High and LMEselect Trading Low for all contracts that have traded during the day. Off book trades resulting from Cross Order execution are not used in the calculation. *)
    Record t := {
      trading_venue : list byte;
      time_of_event : N;
      tradable_instrument_id : N;
      open_price : N;
      trade_high : N;
      trade_low : N;
      closing_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_venue record) = 2 /\
      (time_of_event record < 256 ^ N.of_nat 8)%N /\
      (tradable_instrument_id record < 256 ^ N.of_nat 8)%N /\
      (open_price record < 256 ^ N.of_nat 8)%N /\
      (trade_high record < 256 ^ N.of_nat 8)%N /\
      (trade_low record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (trading_venue record) ++
      encode_uint 8 (time_of_event record) ++
      encode_uint 8 (tradable_instrument_id record) ++
      encode_uint 8 (open_price record) ++
      encode_uint 8 (trade_high record) ++
      encode_uint 8 (trade_low record) ++
      encode_uint 8 (closing_price record).

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
                  | Some (open_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_high_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (trade_low_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (closing_price_value, bytes) =>
                                  Some ({| trading_venue := trading_venue_value; time_of_event := time_of_event_value; tradable_instrument_id := tradable_instrument_id_value; open_price := open_price_value; trade_high := trade_high_value; trade_low := trade_low_value; closing_price := closing_price_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 50.
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
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeStatisticsEndOfDayMessage.

End LmeSelectReferenceDataV418.
