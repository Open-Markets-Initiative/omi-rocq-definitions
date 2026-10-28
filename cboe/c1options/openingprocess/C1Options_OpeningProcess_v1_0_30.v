From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Opening Process

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
      - the dispatch that chooses a message by its type
      - a run filling what frames it
  *)

Module C1OptionsOpeningProcessV1030.

  Module PacketHeader.

    Record t := {
      length_ : N;
      message_count : N;
      unit_ : N;
      sequence : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (length_ record < 256 ^ N.of_nat 2)%N /\
      (message_count record < 256 ^ N.of_nat 1)%N /\
      (unit_ record < 256 ^ N.of_nat 1)%N /\
      (sequence record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (length_ record) ++
      encode_uint 1 (message_count record) ++
      encode_uint 1 (unit_ record) ++
      encode_uint 4 (sequence record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (length__value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (unit__value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (sequence_value, bytes) =>
                      Some ({| length_ := length__value; message_count := message_count_value; unit_ := unit__value; sequence := sequence_value |}, bytes)
                  end
              end
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

  End PacketHeader.

  Module MessageHeader.

    Record t := {
      message_length : N;
      message_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 1)%N /\
      (message_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (message_length record) ++
      encode_uint 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  Module TimeReferenceMessage.

    (** The Time Reference message is used to provide a midnight reference point for recipients of the feed. *)
    Record t := {
      midnight_reference : N;
      time_reference : N;
      time_offset : N;
      trade_date : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (midnight_reference record < 256 ^ N.of_nat 4)%N /\
      (time_reference record < 256 ^ N.of_nat 4)%N /\
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      (trade_date record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (midnight_reference record) ++
      encode_uint 4 (time_reference record) ++
      encode_uint 4 (time_offset record) ++
      encode_uint 4 (trade_date record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (midnight_reference_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (time_reference_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (time_offset_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_date_value, bytes) =>
                      Some ({| midnight_reference := midnight_reference_value; time_reference := time_reference_value; time_offset := time_offset_value; trade_date := trade_date_value |}, bytes)
                  end
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

  End TimeReferenceMessage.

  Module TimeMessage.

    (** A Time message is sent whenever the source time for a unit passes over a second boundary. *)
    Record t := {
      time : N;
      epoch_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time record < 256 ^ N.of_nat 4)%N /\
      (epoch_time record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time record) ++
      encode_uint 4 (epoch_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (epoch_time_value, bytes) =>
              Some ({| time := time_value; epoch_time := epoch_time_value |}, bytes)
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

  End TimeMessage.

  Module OptionsAuctionUpdateMessage.

    (** Options Auction Update messages are used to disseminate price and size information and Composite Market bid and offer prices during Opening and Re-Opening (halt) auctions on the Cboe Options Exchange. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      auction_type : list byte;
      reference_price : N;
      buy_contracts : N;
      sell_contracts : N;
      indicative_price : N;
      auction_only_price : N;
      opening_condition : list byte;
      composite_market_bid_price : N;
      composite_market_offer_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      (reference_price record < 256 ^ N.of_nat 8)%N /\
      (buy_contracts record < 256 ^ N.of_nat 4)%N /\
      (sell_contracts record < 256 ^ N.of_nat 4)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (auction_only_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (opening_condition record) = 1 /\
      (composite_market_bid_price record < 256 ^ N.of_nat 8)%N /\
      (composite_market_offer_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (reference_price record) ++
      encode_uint 4 (buy_contracts record) ++
      encode_uint 4 (sell_contracts record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 8 (auction_only_price record) ++
      encode_bytes 1 (opening_condition record) ++
      encode_uint 8 (composite_market_bid_price record) ++
      encode_uint 8 (composite_market_offer_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (reference_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (buy_contracts_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (sell_contracts_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (indicative_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (auction_only_price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (opening_condition_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (composite_market_bid_price_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (composite_market_offer_price_value, bytes) =>
                                                  Some ({| time_offset := time_offset_value; symbol := symbol_value; auction_type := auction_type_value; reference_price := reference_price_value; buy_contracts := buy_contracts_value; sell_contracts := sell_contracts_value; indicative_price := indicative_price_value; auction_only_price := auction_only_price_value; opening_condition := opening_condition_value; composite_market_bid_price := composite_market_bid_price_value; composite_market_offer_price := composite_market_offer_price_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
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
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OptionsAuctionUpdateMessage.

  Module AuctionSummaryMessage.

    (** Auction Summary messages are used to disseminate the results of an auction. An Opening or Re-Opening Auction Summary message for each symbol is sent at the conclusion of its Opening or Re-Opening auction and represents the Cboe Opening Price. *)
    Record t := {
      time_offset : N;
      symbol : list byte;
      auction_type : list byte;
      price : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 8 /\
      Datatypes.length (auction_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          Some ({| time_offset := time_offset_value; symbol := symbol_value; auction_type := auction_type_value; price := price_value; quantity := quantity_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionSummaryMessage.

  Module WidthUpdateMessage.

    (** The Width Update message is used to communicate the opening quote width multiplier. *)
    Record t := {
      time_offset : N;
      underlying : list byte;
      width_type : list byte;
      multiplier : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (underlying record) = 8 /\
      Datatypes.length (width_type record) = 1 /\
      (multiplier record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 8 (underlying record) ++
      encode_bytes 1 (width_type record) ++
      encode_uint 4 (multiplier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (underlying_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (width_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (multiplier_value, bytes) =>
                      Some ({| time_offset := time_offset_value; underlying := underlying_value; width_type := width_type_value; multiplier := multiplier_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 17.
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

  End WidthUpdateMessage.

  Module SymbolMappingMessage.

    (** A Symbol Mapping message is used to map the 6 character multicast feed symbol field to an OSI symbol. *)
    Record t := {
      feed_symbol : list byte;
      osi_symbol : list byte;
      symbol_condition : list byte;
      underlying : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (feed_symbol record) = 6 /\
      Datatypes.length (osi_symbol record) = 21 /\
      Datatypes.length (symbol_condition record) = 1 /\
      Datatypes.length (underlying record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (feed_symbol record) ++
      encode_bytes 21 (osi_symbol record) ++
      encode_bytes 1 (symbol_condition record) ++
      encode_bytes 8 (underlying record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (feed_symbol_value, bytes) =>
          match decode_bytes 21 bytes with
          | None => None
          | Some (osi_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (symbol_condition_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (underlying_value, bytes) =>
                      Some ({| feed_symbol := feed_symbol_value; osi_symbol := osi_symbol_value; symbol_condition := symbol_condition_value; underlying := underlying_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 bound_3]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SymbolMappingMessage.

  Module EndOfSessionMessage.

    (** The End of Session message is sent for the feed when all the units have shut down. *)
    Record t := {
      time_offset : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          Some ({| time_offset := time_offset_value |}, bytes)
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

  End EndOfSessionMessage.

  Module SoqStrikeRangeUpdateMessage.

    (** The SOQ Strike Range Update message is only available on the C1 Exchange. This message disseminates the minimum and maximum strike prices of the price range used to calculate the Special Opening Quote (SOQ) on a Volatility Settlement date. *)
    Record t := {
      time_offset : N;
      soq_identifier : list byte;
      lower_strike_price : N;
      upper_strike_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (time_offset record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (soq_identifier record) = 20 /\
      (lower_strike_price record < 256 ^ N.of_nat 8)%N /\
      (upper_strike_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (time_offset record) ++
      encode_bytes 20 (soq_identifier record) ++
      encode_uint 8 (lower_strike_price record) ++
      encode_uint 8 (upper_strike_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (time_offset_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (soq_identifier_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (lower_strike_price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (upper_strike_price_value, bytes) =>
                      Some ({| time_offset := time_offset_value; soq_identifier := soq_identifier_value; lower_strike_price := lower_strike_price_value; upper_strike_price := upper_strike_price_value |}, bytes)
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

  End SoqStrikeRangeUpdateMessage.

  Module ConstituentSymbolMappingMessage.

    (** The Constituent Symbol Mapping message is only available on the C1 Exchange. This message is used to communicate which options series (if any) are Constituent Series in a Volatility Settlement Special Opening Quote (SOQ). *)
    Record t := {
      feed_symbol : list byte;
      osi_symbol : list byte;
      symbol_condition : list byte;
      underlying : list byte;
      soq_identifier : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (feed_symbol record) = 6 /\
      Datatypes.length (osi_symbol record) = 21 /\
      Datatypes.length (symbol_condition record) = 1 /\
      Datatypes.length (underlying record) = 8 /\
      Datatypes.length (soq_identifier record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 6 (feed_symbol record) ++
      encode_bytes 21 (osi_symbol record) ++
      encode_bytes 1 (symbol_condition record) ++
      encode_bytes 8 (underlying record) ++
      encode_bytes 20 (soq_identifier record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 6 bytes with
      | None => None
      | Some (feed_symbol_value, bytes) =>
          match decode_bytes 21 bytes with
          | None => None
          | Some (osi_symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (symbol_condition_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (underlying_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (soq_identifier_value, bytes) =>
                          Some ({| feed_symbol := feed_symbol_value; osi_symbol := osi_symbol_value; symbol_condition := symbol_condition_value; underlying := underlying_value; soq_identifier := soq_identifier_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ConstituentSymbolMappingMessage.

End C1OptionsOpeningProcessV1030.
