From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Canadian Securities Exchange CSE2 Multicast Market Data Retransmission

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
      - a run counted by a field
  *)

Module Cse2RetransmissionV16.

  Module BlockHeader.

    (** Prefix of a block of messages, carrying the unique information to identify and route them *)
    Record t := {
      block_length : N;
      block_number_of_messages : N;
      block_start_sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (block_length record < 256 ^ N.of_nat 2)%N /\
      (block_number_of_messages record < 256 ^ N.of_nat 1)%N /\
      (block_start_sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (block_length record) ++
      encode_uint 1 (block_number_of_messages record) ++
      encode_uint 4 (block_start_sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (block_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (block_number_of_messages_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (block_start_sequence_value, bytes) =>
                  Some ({| block_length := block_length_value; block_number_of_messages := block_number_of_messages_value; block_start_sequence := block_start_sequence_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 7.
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

  End BlockHeader.

  Module MessageHeader.

    (** Two byte sub header prefixing every message, carrying its length and its type *)
    Record t := {
      sub_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (sub_length record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (sub_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (sub_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| sub_length := sub_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module TimeMessage.

    (** Anchors the feed clock. Every following message states its own time as nanoseconds elapsed since this message. *)
    Record t := {
      second : N;
      millisecond : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (second record < 256 ^ N.of_nat 4)%N /\
      (millisecond record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (second record) ++
      encode_uint 2 (millisecond record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (second_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (millisecond_value, bytes) =>
              Some ({| second := second_value; millisecond := millisecond_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TimeMessage.

  Module SystemEventMessage.

    (** Signals a market or data feed handler event, either for the system as a whole or for one symbol group. *)
    Record t := {
      time_offset : N;
      group : N;
      event_code : list byte;
      exchange_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (group record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1 /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 8 (group record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 8 (exchange_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exchange_timestamp_value, bytes) =>
                      Some ({| time_offset := time_offset_value; group := group_value; event_code := event_code_value; exchange_timestamp := exchange_timestamp_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 21.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module SymbolDirectoryMessage.

    (** Static properties of a symbol. Sent for every symbol in the morning, and again during the day if a symbol changes. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      cusip : list byte;
      sec_name : list byte;
      currency : list byte;
      stock_group : N;
      listing : N;
      expiry : N;
      lot_size : N;
      settlement_term : list byte;
      listing_market : list byte;
      previous_closing_price : N;
      listing_tier : N;
      market_maker_name : list byte;
      market_maker_phone_number : list byte;
      full_sec_name : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (cusip record) = 12 /\
      Datatypes.length (sec_name record) = 15 /\
      Datatypes.length (currency record) = 3 /\
      (stock_group record < 256 ^ N.of_nat 8)%N /\
      (listing record < 256 ^ N.of_nat 8)%N /\
      (expiry record < 256 ^ N.of_nat 8)%N /\
      (lot_size record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (settlement_term record) = 8 /\
      Datatypes.length (listing_market record) = 1 /\
      (previous_closing_price record < 256 ^ N.of_nat 4)%N /\
      (listing_tier record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (market_maker_name record) = 20 /\
      Datatypes.length (market_maker_phone_number record) = 12 /\
      Datatypes.length (full_sec_name record) = 75.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 12 (symbol record) ++
      encode_bytes 12 (cusip record) ++
      encode_bytes 15 (sec_name record) ++
      encode_bytes 3 (currency record) ++
      encode_uint 8 (stock_group record) ++
      encode_uint 8 (listing record) ++
      encode_uint 8 (expiry record) ++
      encode_uint 4 (lot_size record) ++
      encode_bytes 8 (settlement_term record) ++
      encode_bytes 1 (listing_market record) ++
      encode_uint 4 (previous_closing_price record) ++
      encode_uint 1 (listing_tier record) ++
      encode_bytes 20 (market_maker_name record) ++
      encode_bytes 12 (market_maker_phone_number record) ++
      encode_bytes 75 (full_sec_name record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (cusip_value, bytes) =>
                  match decode_bytes 15 bytes with
                  | None => None
                  | Some (sec_name_value, bytes) =>
                      match decode_bytes 3 bytes with
                      | None => None
                      | Some (currency_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (stock_group_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (listing_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (expiry_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (lot_size_value, bytes) =>
                                          match decode_bytes 8 bytes with
                                          | None => None
                                          | Some (settlement_term_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (listing_market_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (previous_closing_price_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (listing_tier_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (market_maker_name_value, bytes) =>
                                                              match decode_bytes 12 bytes with
                                                              | None => None
                                                              | Some (market_maker_phone_number_value, bytes) =>
                                                                  match decode_bytes 75 bytes with
                                                                  | None => None
                                                                  | Some (full_sec_name_value, bytes) =>
                                                                      Some ({| time_offset := time_offset_value; symbol := symbol_value; cusip := cusip_value; sec_name := sec_name_value; currency := currency_value; stock_group := stock_group_value; listing := listing_value; expiry := expiry_value; lot_size := lot_size_value; settlement_term := settlement_term_value; listing_market := listing_market_value; previous_closing_price := previous_closing_price_value; listing_tier := listing_tier_value; market_maker_name := market_maker_name_value; market_maker_phone_number := market_maker_phone_number_value; full_sec_name := full_sec_name_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 195.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolDirectoryMessage.

  Module SymbolDynamicsMessage.

    (** Values and rules for a symbol that can be updated intra-day. Sent for every symbol in the morning, and again during the day if a symbol changes. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      settlement_term : list byte;
      gmf_setting : list byte;
      gmf_volume : N;
      anonymous_setting : list byte;
      moc_eligible : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (settlement_term record) = 8 /\
      Datatypes.length (gmf_setting record) = 1 /\
      (gmf_volume record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (anonymous_setting record) = 1 /\
      Datatypes.length (moc_eligible record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 12 (symbol record) ++
      encode_bytes 8 (settlement_term record) ++
      encode_bytes 1 (gmf_setting record) ++
      encode_uint 8 (gmf_volume record) ++
      encode_bytes 1 (anonymous_setting record) ++
      encode_bytes 1 (moc_eligible record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (settlement_term_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (gmf_setting_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (gmf_volume_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (anonymous_setting_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (moc_eligible_value, bytes) =>
                                  Some ({| time_offset := time_offset_value; symbol := symbol_value; settlement_term := settlement_term_value; gmf_setting := gmf_setting_value; gmf_volume := gmf_volume_value; anonymous_setting := anonymous_setting_value; moc_eligible := moc_eligible_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolDynamicsMessage.

  Module TradingActionMessage.

    (** Current trading state for a symbol. A symbol suspended intra-day with "V" is unsuspended with "N". *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      trading_state : list byte;
      exchange_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      Datatypes.length (trading_state record) = 1 /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 12 (symbol record) ++
      encode_bytes 1 (trading_state record) ++
      encode_uint 8 (exchange_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_state_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exchange_timestamp_value, bytes) =>
                      Some ({| time_offset := time_offset_value; symbol := symbol_value; trading_state := trading_state_value; exchange_timestamp := exchange_timestamp_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 25.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingActionMessage.

  Module AddOrderMessage.

    (** A new order added to the displayed book. *)
    Record t := {
      time_offset : N;
      order_number : list byte;
      order_verb : list byte;
      quantity : N;
      symbol : list byte;
      price : N;
      firm_id : list byte;
      settlement_term : list byte;
      odd_lot_flag : list byte;
      exchange_timestamp : N;
      priority_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_number record) = 18 /\
      Datatypes.length (order_verb record) = 1 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_id record) = 3 /\
      Datatypes.length (settlement_term record) = 8 /\
      Datatypes.length (odd_lot_flag record) = 1 /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N /\
      (priority_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 18 (order_number record) ++
      encode_bytes 1 (order_verb record) ++
      encode_uint 4 (quantity record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record) ++
      encode_bytes 3 (firm_id record) ++
      encode_bytes 8 (settlement_term record) ++
      encode_bytes 1 (odd_lot_flag record) ++
      encode_uint 8 (exchange_timestamp record) ++
      encode_uint 8 (priority_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_verb_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (symbol_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (firm_id_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (settlement_term_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (odd_lot_flag_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (exchange_timestamp_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (priority_timestamp_value, bytes) =>
                                                  Some ({| time_offset := time_offset_value; order_number := order_number_value; order_verb := order_verb_value; quantity := quantity_value; symbol := symbol_value; price := price_value; firm_id := firm_id_value; settlement_term := settlement_term_value; odd_lot_flag := odd_lot_flag_value; exchange_timestamp := exchange_timestamp_value; priority_timestamp := priority_timestamp_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module OrderExecutedMessage.

    (** An order on the book executed in whole or in part at the price it was displayed at. *)
    Record t := {
      time_offset : N;
      order_number : list byte;
      executed_quantity : N;
      match_number : list byte;
      exchange_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_number record) = 18 /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (match_number record) = 18 /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 18 (order_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_bytes 18 (match_number record) ++
      encode_uint 8 (exchange_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_bytes 18 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exchange_timestamp_value, bytes) =>
                          Some ({| time_offset := time_offset_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; exchange_timestamp := exchange_timestamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 52.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** An order on the book executed in whole or in part at a price other than the one it was displayed at. *)
    Record t := {
      time_offset : N;
      order_number : list byte;
      executed_quantity : N;
      match_number : list byte;
      execution_price : N;
      exchange_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_number record) = 18 /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (match_number record) = 18 /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 18 (order_number record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_bytes 18 (match_number record) ++
      encode_uint 4 (execution_price record) ++
      encode_uint 8 (exchange_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_bytes 18 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (execution_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (exchange_timestamp_value, bytes) =>
                              Some ({| time_offset := time_offset_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; execution_price := execution_price_value; exchange_timestamp := exchange_timestamp_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceMessage.

  Module TradeMessage.

    (** A trade that does not change the displayed book, carrying the full attribution and classification of the execution. *)
    Record t := {
      time_offset : N;
      executed_quantity : N;
      symbol : list byte;
      execution_price : N;
      match_number : list byte;
      firm_id : list byte;
      contra_firm_id : list byte;
      settlement_term : list byte;
      trade_attribute : list byte;
      cross_type : list byte;
      odd_lot_flag : list byte;
      sets_the_last_price : list byte;
      exchange_timestamp : N;
      opening_trade : list byte;
      ccp_session_trade : list byte;
      moc_trade_marker : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (execution_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (match_number record) = 18 /\
      Datatypes.length (firm_id record) = 3 /\
      Datatypes.length (contra_firm_id record) = 3 /\
      Datatypes.length (settlement_term record) = 8 /\
      Datatypes.length (trade_attribute record) = 1 /\
      Datatypes.length (cross_type record) = 1 /\
      Datatypes.length (odd_lot_flag record) = 1 /\
      Datatypes.length (sets_the_last_price record) = 1 /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (opening_trade record) = 1 /\
      Datatypes.length (ccp_session_trade record) = 1 /\
      Datatypes.length (moc_trade_marker record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_uint 4 (executed_quantity record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (execution_price record) ++
      encode_bytes 18 (match_number record) ++
      encode_bytes 3 (firm_id record) ++
      encode_bytes 3 (contra_firm_id record) ++
      encode_bytes 8 (settlement_term record) ++
      encode_bytes 1 (trade_attribute record) ++
      encode_bytes 1 (cross_type record) ++
      encode_bytes 1 (odd_lot_flag record) ++
      encode_bytes 1 (sets_the_last_price record) ++
      encode_uint 8 (exchange_timestamp record) ++
      encode_bytes 1 (opening_trade record) ++
      encode_bytes 1 (ccp_session_trade record) ++
      encode_bytes 1 (moc_trade_marker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (symbol_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (execution_price_value, bytes) =>
                      match decode_bytes 18 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (firm_id_value, bytes) =>
                              match decode_bytes 3 bytes with
                              | None => None
                              | Some (contra_firm_id_value, bytes) =>
                                  match decode_bytes 8 bytes with
                                  | None => None
                                  | Some (settlement_term_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_attribute_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (cross_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (odd_lot_flag_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (sets_the_last_price_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (exchange_timestamp_value, bytes) =>
                                                          match decode_bytes 1 bytes with
                                                          | None => None
                                                          | Some (opening_trade_value, bytes) =>
                                                              match decode_bytes 1 bytes with
                                                              | None => None
                                                              | Some (ccp_session_trade_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (moc_trade_marker_value, bytes) =>
                                                                      Some ({| time_offset := time_offset_value; executed_quantity := executed_quantity_value; symbol := symbol_value; execution_price := execution_price_value; match_number := match_number_value; firm_id := firm_id_value; contra_firm_id := contra_firm_id_value; settlement_term := settlement_term_value; trade_attribute := trade_attribute_value; cross_type := cross_type_value; odd_lot_flag := odd_lot_flag_value; sets_the_last_price := sets_the_last_price_value; exchange_timestamp := exchange_timestamp_value; opening_trade := opening_trade_value; ccp_session_trade := ccp_session_trade_value; moc_trade_marker := moc_trade_marker_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 bound_15]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module BrokenTradeMessage.

    (** A previously transmitted execution that has been broken, naming the match number it cancels. *)
    Record t := {
      time_offset : N;
      match_number : list byte;
      reason : list byte;
      exchange_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (match_number record) = 18 /\
      Datatypes.length (reason record) = 1 /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 18 (match_number record) ++
      encode_bytes 1 (reason record) ++
      encode_uint 8 (exchange_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (match_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reason_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (exchange_timestamp_value, bytes) =>
                      Some ({| time_offset := time_offset_value; match_number := match_number_value; reason := reason_value; exchange_timestamp := exchange_timestamp_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BrokenTradeMessage.

  Module OrderDeleteMessage.

    (** An order cancelled and removed from the displayed book. *)
    Record t := {
      time_offset : N;
      order_number : list byte;
      exchange_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_number record) = 18 /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 18 (order_number record) ++
      encode_uint 8 (exchange_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (exchange_timestamp_value, bytes) =>
                  Some ({| time_offset := time_offset_value; order_number := order_number_value; exchange_timestamp := exchange_timestamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderDeleteMessage.

  Module OrderReplaceMessage.

    (** An order on the book replaced with a new quantity and price, keeping its order number. *)
    Record t := {
      time_offset : N;
      order_number : list byte;
      quantity : N;
      price : N;
      exchange_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_number record) = 18 /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 18 (order_number record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (exchange_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 18 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (quantity_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (exchange_timestamp_value, bytes) =>
                          Some ({| time_offset := time_offset_value; order_number := order_number_value; quantity := quantity_value; price := price_value; exchange_timestamp := exchange_timestamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderReplaceMessage.

  Module BestBidOfferMessage.

    (** The best bid and offer for a symbol with the quantity at each. During an auction with an indicative price set, the indicative price overwrites both sides. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      best_bid : N;
      best_bid_size : N;
      best_offer : N;
      best_offer_size : N;
      exchange_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (best_bid record < 256 ^ N.of_nat 4)%N /\
      (best_bid_size record < 256 ^ N.of_nat 4)%N /\
      (best_offer record < 256 ^ N.of_nat 4)%N /\
      (best_offer_size record < 256 ^ N.of_nat 4)%N /\
      (exchange_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (best_bid record) ++
      encode_uint 4 (best_bid_size record) ++
      encode_uint 4 (best_offer record) ++
      encode_uint 4 (best_offer_size record) ++
      encode_uint 8 (exchange_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (best_bid_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (best_bid_size_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (best_offer_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (best_offer_size_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (exchange_timestamp_value, bytes) =>
                                  Some ({| time_offset := time_offset_value; symbol := symbol_value; best_bid := best_bid_value; best_bid_size := best_bid_size_value; best_offer := best_offer_value; best_offer_size := best_offer_size_value; exchange_timestamp := exchange_timestamp_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End BestBidOfferMessage.

  Module ClosingPriceMessage.

    (** The closing price for a symbol. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 12 /\
      (price record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 12 (symbol record) ++
      encode_uint 4 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 12 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  Some ({| time_offset := time_offset_value; symbol := symbol_value; price := price_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClosingPriceMessage.

  Module GeneralMessage.

    (** Free text bulletin from the exchange. *)
    Record t := {
      time_offset : N;
      message_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (message_text record) = 128.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 128 (message_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 128 bytes with
          | None => None
          | Some (message_text_value, bytes) =>
              Some ({| time_offset := time_offset_value; message_text := message_text_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 132.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End GeneralMessage.

  Module LoginRequestMessage.

    (** The first message a client sends once a Tcp connection to the Retransmission or Spin server is established. *)
    Record t := {
      user_id : list byte;
      password : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 16 /\
      Datatypes.length (password record) = 16.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (user_id record) ++
      encode_bytes 16 (password record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 16 bytes with
          | None => None
          | Some (password_value, bytes) =>
              Some ({| user_id := user_id_value; password := password_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginRequestMessage.

  Module LoginResponseMessage.

    (** Reply to a Login Request. Always "Y": an invalid user id or password is signalled by the exchange closing the socket after 5 seconds without a response. *)
    Record t := {
      user_id : list byte;
      login_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (user_id record) = 16 /\
      Datatypes.length (login_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 16 (user_id record) ++
      encode_bytes 1 (login_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 16 bytes with
      | None => None
      | Some (user_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (login_status_value, bytes) =>
              Some ({| user_id := user_id_value; login_status := login_status_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LoginResponseMessage.

  Module RetransmissionRequestMessage.

    (** Asks the exchange to replay a range of sequenced messages the client missed. *)
    Record t := {
      start_sequence : N;
      number_of_messages : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_sequence record < 256 ^ N.of_nat 4)%N /\
      (number_of_messages record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (start_sequence record) ++
      encode_uint 4 (number_of_messages record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (start_sequence_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (number_of_messages_value, bytes) =>
              Some ({| start_sequence := start_sequence_value; number_of_messages := number_of_messages_value |}, bytes)
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

  End RetransmissionRequestMessage.

  Module RetransmissionResponseMessage.

    (** States whether the requested retransmission will follow. The replayed messages are framed exactly as the multicast feed sent them. *)
    Record t := {
      start_sequence : N;
      number_of_messages : N;
      retransmission_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (start_sequence record < 256 ^ N.of_nat 4)%N /\
      (number_of_messages record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (retransmission_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (start_sequence record) ++
      encode_uint 4 (number_of_messages record) ++
      encode_bytes 1 (retransmission_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (start_sequence_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (number_of_messages_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (retransmission_status_value, bytes) =>
                  Some ({| start_sequence := start_sequence_value; number_of_messages := number_of_messages_value; retransmission_status := retransmission_status_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 9.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RetransmissionResponseMessage.

  Module SpinRequestMessage.

    (** Asks for a snapshot of the whole order book, used by a client that has lost its book rather than detected a gap. *)
    Record t := {
      client_identifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_identifier record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (client_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (client_identifier_value, bytes) =>
          Some ({| client_identifier := client_identifier_value |}, bytes)
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

  End SpinRequestMessage.

  Module SpinResponseMessage.

    (** Brackets a book snapshot. The exchange acknowledges the spin request with "S", retransmits the book over the same socket, then sends a second response with "E" to mark the end. *)
    Record t := {
      client_identifier : N;
      spin_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_identifier record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (spin_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (client_identifier record) ++
      encode_bytes 1 (spin_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (client_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (spin_status_value, bytes) =>
              Some ({| client_identifier := client_identifier_value; spin_status := spin_status_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 5.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SpinResponseMessage.

  Module HeartbeatMessage.

    (** Sent by the exchange once per defined period for line integrity testing. The client must send the same message back on receipt, and two consecutive missed heartbeats terminate the connection. *)
    Record t := {
      client_identifier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (client_identifier record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (client_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (client_identifier_value, bytes) =>
          Some ({| client_identifier := client_identifier_value |}, bytes)
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

  End HeartbeatMessage.

End Cse2RetransmissionV16.
