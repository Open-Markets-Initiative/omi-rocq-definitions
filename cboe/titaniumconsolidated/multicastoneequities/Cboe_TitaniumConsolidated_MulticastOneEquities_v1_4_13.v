From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Multicast One Equities

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
      - a field read in bits
      - a run counted by a field
  *)

Module CboeTitaniumConsolidatedMulticastOneEquitiesV1413.

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

  Module ClearQuoteMessage.

    (** The Clear Quote message instructs feed recipients to clear all quotes and Summary and/or ADAP information for the specified symbol on the specified market(s). *)
    Record t := {
      last_update_timestamp : N;
      symbol_short : list byte;
      market_center : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (market_center record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (market_center record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  Some ({| last_update_timestamp := last_update_timestamp_value; symbol_short := symbol_short_value; market_center := market_center_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClearQuoteMessage.

  Module ExpandedClearQuoteMessage.

    (** The Expanded Clear Quote message instructs feed recipients to clear all quotes and Summary and/or ADAP information for the specified symbol on the specified market(s). Used when the symbol exceeds eight characters. *)
    Record t := {
      last_update_timestamp : N;
      symbol_long : list byte;
      market_center : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 14 /\
      Datatypes.length (market_center record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 14 (symbol_long record) ++
      encode_bytes 1 (market_center record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  Some ({| last_update_timestamp := last_update_timestamp_value; symbol_long := symbol_long_value; market_center := market_center_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedClearQuoteMessage.

  Module ExpandedFractionalSymbolSummaryMessage.

    (** The Expanded Fractional Symbol Summary message delivers the Cboe consolidated best bid/offer and total executed volume across all applicable Cboe One Canada books. Used when the symbol exceeds eight characters. *)
    Record t := {
      last_update_timestamp : N;
      symbol_long : list byte;
      cboe_cumulative_executed_volume : N;
      consolidated_best_bid_price : N;
      consolidated_best_bid_quantity : N;
      consolidated_best_ask_price : N;
      consolidated_best_ask_quantity : N;
      national_cumulative_volume : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 14 /\
      (cboe_cumulative_executed_volume record < 256 ^ N.of_nat 8)%N /\
      (consolidated_best_bid_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_best_bid_quantity record < 256 ^ N.of_nat 8)%N /\
      (consolidated_best_ask_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_best_ask_quantity record < 256 ^ N.of_nat 8)%N /\
      (national_cumulative_volume record < 256 ^ N.of_nat 8)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 14 (symbol_long record) ++
      encode_uint 8 (cboe_cumulative_executed_volume record) ++
      encode_uint 8 (consolidated_best_bid_price record) ++
      encode_uint 8 (consolidated_best_bid_quantity record) ++
      encode_uint 8 (consolidated_best_ask_price record) ++
      encode_uint 8 (consolidated_best_ask_quantity record) ++
      encode_uint 8 (national_cumulative_volume record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (cboe_cumulative_executed_volume_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consolidated_best_bid_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (consolidated_best_bid_quantity_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (consolidated_best_ask_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (consolidated_best_ask_quantity_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (national_cumulative_volume_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (reserved_1_value, bytes) =>
                                          Some ({| last_update_timestamp := last_update_timestamp_value; symbol_long := symbol_long_value; cboe_cumulative_executed_volume := cboe_cumulative_executed_volume_value; consolidated_best_bid_price := consolidated_best_bid_price_value; consolidated_best_bid_quantity := consolidated_best_bid_quantity_value; consolidated_best_ask_price := consolidated_best_ask_price_value; consolidated_best_ask_quantity := consolidated_best_ask_quantity_value; national_cumulative_volume := national_cumulative_volume_value; reserved_1 := reserved_1_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedFractionalSymbolSummaryMessage.

  Module BestQuoteUpdateMessage.

    (** The Best Quote Update message is used to update one side of the Cboe consolidated quote information for a symbol. *)
    Record t := {
      last_update_timestamp : N;
      symbol_short : list byte;
      side_indicator : list byte;
      consolidated_best_quote_price : N;
      consolidated_quote_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (side_indicator record) = 1 /\
      (consolidated_best_quote_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_quote_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 8 (consolidated_best_quote_price record) ++
      encode_uint 8 (consolidated_quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consolidated_best_quote_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (consolidated_quote_quantity_value, bytes) =>
                          Some ({| last_update_timestamp := last_update_timestamp_value; symbol_short := symbol_short_value; side_indicator := side_indicator_value; consolidated_best_quote_price := consolidated_best_quote_price_value; consolidated_quote_quantity := consolidated_quote_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 33.
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

  End BestQuoteUpdateMessage.

  Module ExpandedBestQuoteUpdateMessage.

    (** The Expanded Best Quote Update message is used to update one side of the Cboe consolidated quote information for a symbol. Used when the symbol exceeds eight characters. *)
    Record t := {
      last_update_timestamp : N;
      symbol_long : list byte;
      side_indicator : list byte;
      consolidated_best_quote_price : N;
      consolidated_quote_quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (last_update_timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 14 /\
      Datatypes.length (side_indicator record) = 1 /\
      (consolidated_best_quote_price record < 256 ^ N.of_nat 8)%N /\
      (consolidated_quote_quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (last_update_timestamp record) ++
      encode_bytes 14 (symbol_long record) ++
      encode_bytes 1 (side_indicator record) ++
      encode_uint 8 (consolidated_best_quote_price record) ++
      encode_uint 8 (consolidated_quote_quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (last_update_timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_indicator_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (consolidated_best_quote_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (consolidated_quote_quantity_value, bytes) =>
                          Some ({| last_update_timestamp := last_update_timestamp_value; symbol_long := symbol_long_value; side_indicator := side_indicator_value; consolidated_best_quote_price := consolidated_best_quote_price_value; consolidated_quote_quantity := consolidated_quote_quantity_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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

  End ExpandedBestQuoteUpdateMessage.

  Module CboeMarketStatusMessage.

    (** The Cboe Market Status message is disseminated to reflect a change in the status of a market. *)
    Record t := {
      timestamp : N;
      market_center : list byte;
      market_status : list byte;
      session_indicator : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (market_status record) = 1 /\
      Datatypes.length (session_indicator record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (market_status record) ++
      encode_bytes 1 (session_indicator record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_center_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (session_indicator_value, bytes) =>
                      Some ({| timestamp := timestamp_value; market_center := market_center_value; market_status := market_status_value; session_indicator := session_indicator_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CboeMarketStatusMessage.

  Module ShortUpdateAdapBlock.

    (** Short Update ADAP Block *)
    Record t := {
      market_center : list byte;
      side : list byte;
      price_short : N;
      quantity_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (price_short record < 256 ^ N.of_nat 4)%N /\
      (quantity_short record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (price_short record) ++
      encode_uint 4 (quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_short_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_short_value, bytes) =>
                      Some ({| market_center := market_center_value; side := side_value; price_short := price_short_value; quantity_short := quantity_short_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortUpdateAdapBlock.

  Module LongUpdateAdapBlock.

    (** Long Update ADAP Block *)
    Record t := {
      market_center : list byte;
      side : list byte;
      price_long : N;
      quantity_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (quantity_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_long_value, bytes) =>
                      Some ({| market_center := market_center_value; side := side_value; price_long := price_long_value; quantity_long := quantity_long_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongUpdateAdapBlock.

  Module ShortUpdateAdapBlock2.

    (** Short Update ADAP Block *)
    Record t := {
      market_center : list byte;
      side : list byte;
      price_short : N;
      quantity_short : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (price_short record < 256 ^ N.of_nat 4)%N /\
      (quantity_short record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (side record) ++
      encode_uint 4 (price_short record) ++
      encode_uint 4 (quantity_short record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_short_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (quantity_short_value, bytes) =>
                      Some ({| market_center := market_center_value; side := side_value; price_short := price_short_value; quantity_short := quantity_short_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ShortUpdateAdapBlock2.

  Module LongUpdateAdapBlock2.

    (** Long Update ADAP Block *)
    Record t := {
      market_center : list byte;
      side : list byte;
      price_long : N;
      quantity_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (side record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N /\
      (quantity_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price_long record) ++
      encode_uint 8 (quantity_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_center_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (side_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_long_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_long_value, bytes) =>
                      Some ({| market_center := market_center_value; side := side_value; price_long := price_long_value; quantity_long := quantity_long_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End LongUpdateAdapBlock2.

  Module RpiMessage.

    (** The Retail Price Improvement (RPI) message is a retail liquidity indicator that includes symbol and side, but not price and size. US Only. *)
    Record t := {
      timestamp : N;
      symbol_short : list byte;
      market_center : list byte;
      retail_price_improvement : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (retail_price_improvement record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (retail_price_improvement record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (retail_price_improvement_value, bytes) =>
                      Some ({| timestamp := timestamp_value; symbol_short := symbol_short_value; market_center := market_center_value; retail_price_improvement := retail_price_improvement_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 18.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End RpiMessage.

  Module ExpandedFractionalTradeMessage.

    (** The Expanded Fractional Trade message is identical to the Fractional Trade message described previously, except for the length of the Symbol field which is expanded from 8 to 14. *)
    Record t := {
      transaction_time : N;
      symbol_long : list byte;
      market_center : list byte;
      market_center_execution_id : N;
      last_price : N;
      last_quantity : N;
      cboe_cumulative_executed_volume : N;
      national_cumulative_volume : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 14 /\
      Datatypes.length (market_center record) = 1 /\
      (market_center_execution_id record < 256 ^ N.of_nat 8)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (last_quantity record < 256 ^ N.of_nat 8)%N /\
      (cboe_cumulative_executed_volume record < 256 ^ N.of_nat 8)%N /\
      (national_cumulative_volume record < 256 ^ N.of_nat 8)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 14 (symbol_long record) ++
      encode_bytes 1 (market_center record) ++
      encode_uint 8 (market_center_execution_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 8 (last_quantity record) ++
      encode_uint 8 (cboe_cumulative_executed_volume record) ++
      encode_uint 8 (national_cumulative_volume record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (market_center_execution_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (last_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (last_quantity_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (cboe_cumulative_executed_volume_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (national_cumulative_volume_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (reserved_1_value, bytes) =>
                                          Some ({| transaction_time := transaction_time_value; symbol_long := symbol_long_value; market_center := market_center_value; market_center_execution_id := market_center_execution_id_value; last_price := last_price_value; last_quantity := last_quantity_value; cboe_cumulative_executed_volume := cboe_cumulative_executed_volume_value; national_cumulative_volume := national_cumulative_volume_value; reserved_1 := reserved_1_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 64.
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
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedFractionalTradeMessage.

  Module ExpandedFractionalTradeBreakMessage.

    (** The Expanded Fractional Trade Break message is sent whenever an execution on a Cboe exchange is broken. Used when the symbol exceeds eight characters. *)
    Record t := {
      transaction_time : N;
      symbol_long : list byte;
      market_center : list byte;
      market_center_execution_id : N;
      cboe_cumulative_executed_volume : N;
      national_cumulative_volume : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transaction_time record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 14 /\
      Datatypes.length (market_center record) = 1 /\
      (market_center_execution_id record < 256 ^ N.of_nat 8)%N /\
      (cboe_cumulative_executed_volume record < 256 ^ N.of_nat 8)%N /\
      (national_cumulative_volume record < 256 ^ N.of_nat 8)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transaction_time record) ++
      encode_bytes 14 (symbol_long record) ++
      encode_bytes 1 (market_center record) ++
      encode_uint 8 (market_center_execution_id record) ++
      encode_uint 8 (cboe_cumulative_executed_volume record) ++
      encode_uint 8 (national_cumulative_volume record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transaction_time_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (market_center_execution_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (cboe_cumulative_executed_volume_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (national_cumulative_volume_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reserved_1_value, bytes) =>
                                  Some ({| transaction_time := transaction_time_value; symbol_long := symbol_long_value; market_center := market_center_value; market_center_execution_id := market_center_execution_id_value; cboe_cumulative_executed_volume := cboe_cumulative_executed_volume_value; national_cumulative_volume := national_cumulative_volume_value; reserved_1 := reserved_1_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedFractionalTradeBreakMessage.

  Module TradingStatusMessage.

    (** The Trading Status message is used to indicate the current trading status of a security on a Cboe exchange. *)
    Record t := {
      timestamp : N;
      symbol_short : list byte;
      market_center : list byte;
      trading_status : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reg_sho_action_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol_short := symbol_short_value; market_center := market_center_value; trading_status := trading_status_value; reg_sho_action := reg_sho_action_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradingStatusMessage.

  Module ExpandedTradingStatusMessage.

    (** The Expanded Trading Status message is identical to the Trading Status message described previously, except for the length of the Symbol field which is expanded from 8 to 14. Canada Only. *)
    Record t := {
      timestamp : N;
      symbol_long : list byte;
      market_center : list byte;
      trading_status : list byte;
      reg_sho_action : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 14 /\
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (reg_sho_action record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (symbol_long record) ++
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 1 (reg_sho_action record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (trading_status_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reg_sho_action_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol_long := symbol_long_value; market_center := market_center_value; trading_status := trading_status_value; reg_sho_action := reg_sho_action_value |}, bytes)
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedTradingStatusMessage.

  Module OpeningClosingPriceMessage.

    (** The Opening/Closing Price message is used to indicate the Opening or Closing price of a security on any of the Cboe markets and the primary listing market. *)
    Record t := {
      timestamp : N;
      symbol_short : list byte;
      market_center : list byte;
      open_close_indicator : list byte;
      price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (open_close_indicator record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (open_close_indicator record) ++
      encode_uint 8 (price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (open_close_indicator_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol_short := symbol_short_value; market_center := market_center_value; open_close_indicator := open_close_indicator_value; price_long := price_long_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 26.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OpeningClosingPriceMessage.

  Module ExpandedOpeningClosingPriceMessage.

    (** The Expanded Opening/Closing Price message is identical to the Opening/Closing Price message described previously, except for the length of the Symbol field which is expanded from 8 to 14. Canada Only. *)
    Record t := {
      timestamp : N;
      symbol_long : list byte;
      market_center : list byte;
      open_close_indicator : list byte;
      price_long : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 14 /\
      Datatypes.length (market_center record) = 1 /\
      Datatypes.length (open_close_indicator record) = 1 /\
      (price_long record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (symbol_long record) ++
      encode_bytes 1 (market_center record) ++
      encode_bytes 1 (open_close_indicator record) ++
      encode_uint 8 (price_long record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (market_center_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (open_close_indicator_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_long_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol_long := symbol_long_value; market_center := market_center_value; open_close_indicator := open_close_indicator_value; price_long := price_long_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedOpeningClosingPriceMessage.

  Module FractionalEndOfDaySummaryMessage.

    (** The Fractional End of Day Summary message is used to give a consolidated, high-level overview of a security for the day. *)
    Record t := {
      timestamp : N;
      symbol_short : list byte;
      data_source : list byte;
      opening_price : N;
      closing_price : N;
      high_price : N;
      low_price : N;
      national_cumulative_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_short record) = 8 /\
      Datatypes.length (data_source record) = 1 /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (national_cumulative_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 8 (symbol_short record) ++
      encode_bytes 1 (data_source record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (national_cumulative_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 8 bytes with
          | None => None
          | Some (symbol_short_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (data_source_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (opening_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (high_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (low_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (national_cumulative_volume_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; symbol_short := symbol_short_value; data_source := data_source_value; opening_price := opening_price_value; closing_price := closing_price_value; high_price := high_price_value; low_price := low_price_value; national_cumulative_volume := national_cumulative_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 57.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End FractionalEndOfDaySummaryMessage.

  Module ExpandedFractionalEndOfDaySummaryMessage.

    (** The Expanded Fractional End of Day Summary message is identical to the Fractional End of Day Summary message described previously, except for the length of the Symbol field which is expanded from 8 to 14. Canada Only. *)
    Record t := {
      timestamp : N;
      symbol_long : list byte;
      data_source : list byte;
      opening_price : N;
      closing_price : N;
      high_price : N;
      low_price : N;
      national_cumulative_volume : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol_long record) = 14 /\
      Datatypes.length (data_source record) = 1 /\
      (opening_price record < 256 ^ N.of_nat 8)%N /\
      (closing_price record < 256 ^ N.of_nat 8)%N /\
      (high_price record < 256 ^ N.of_nat 8)%N /\
      (low_price record < 256 ^ N.of_nat 8)%N /\
      (national_cumulative_volume record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 14 (symbol_long record) ++
      encode_bytes 1 (data_source record) ++
      encode_uint 8 (opening_price record) ++
      encode_uint 8 (closing_price record) ++
      encode_uint 8 (high_price record) ++
      encode_uint 8 (low_price record) ++
      encode_uint 8 (national_cumulative_volume record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 14 bytes with
          | None => None
          | Some (symbol_long_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (data_source_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (opening_price_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (closing_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (high_price_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (low_price_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (national_cumulative_volume_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; symbol_long := symbol_long_value; data_source := data_source_value; opening_price := opening_price_value; closing_price := closing_price_value; high_price := high_price_value; low_price := low_price_value; national_cumulative_volume := national_cumulative_volume_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 63.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExpandedFractionalEndOfDaySummaryMessage.

End CboeTitaniumConsolidatedMulticastOneEquitiesV1413.
