From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Athens Exchange Group Athens Exchange Securities Market Real Time Channel

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
      - a length prefix framing what follows
      - a field read in bits
      - a run counted by a field
  *)

Module AthexSecuritiesRealTimeV52.

  Module MessageHeader.

    (** Thirty five character header succeeding the Soh character of every message packet *)
    Record t := {
      vendor_identifier : list byte;
      message_category : list byte;
      message_subcategory : list byte;
      venue_i_d : list byte;
      message_sequence_number : list byte;
      publication_timestamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (vendor_identifier record) = 2 /\
      Datatypes.length (message_category record) = 1 /\
      Datatypes.length (message_subcategory record) = 1 /\
      Datatypes.length (venue_i_d record) = 4 /\
      Datatypes.length (message_sequence_number record) = 7 /\
      Datatypes.length (publication_timestamp record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 2 (vendor_identifier record) ++
      encode_bytes 1 (message_category record) ++
      encode_bytes 1 (message_subcategory record) ++
      encode_bytes 4 (venue_i_d record) ++
      encode_bytes 7 (message_sequence_number record) ++
      encode_bytes 20 (publication_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 2 bytes with
      | None => None
      | Some (vendor_identifier_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_category_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (message_subcategory_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (venue_i_d_value, bytes) =>
                      match decode_bytes 7 bytes with
                      | None => None
                      | Some (message_sequence_number_value, bytes) =>
                          match decode_bytes 20 bytes with
                          | None => None
                          | Some (publication_timestamp_value, bytes) =>
                              Some ({| vendor_identifier := vendor_identifier_value; message_category := message_category_value; message_subcategory := message_subcategory_value; venue_i_d := venue_i_d_value; message_sequence_number := message_sequence_number_value; publication_timestamp := publication_timestamp_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 35.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MessageHeader.

  Module IndexMessage.

    (** Transmitted every time the trading platform calculates the price of a given index *)
    Record t := {
      symbol : list byte;
      index_price : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 15 /\
      Datatypes.length (index_price record) = 9.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (symbol record) ++
      encode_bytes 9 (index_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (index_price_value, bytes) =>
              Some ({| symbol := symbol_value; index_price := index_price_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End IndexMessage.

  Module InstrumentSummaryMessage.

    (** Transmitted for each instrument right after the corresponding market status changes to End of Day *)
    Record t := {
      symbol : list byte;
      opening_price : list byte;
      high : list byte;
      low : list byte;
      last : list byte;
      closing_price : list byte;
      start_of_day_price : list byte;
      total_volume : list byte;
      total_value : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 15 /\
      Datatypes.length (opening_price record) = 9 /\
      Datatypes.length (high record) = 9 /\
      Datatypes.length (low record) = 9 /\
      Datatypes.length (last record) = 9 /\
      Datatypes.length (closing_price record) = 9 /\
      Datatypes.length (start_of_day_price record) = 9 /\
      Datatypes.length (total_volume record) = 17 /\
      Datatypes.length (total_value record) = 17.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (symbol record) ++
      encode_bytes 9 (opening_price record) ++
      encode_bytes 9 (high record) ++
      encode_bytes 9 (low record) ++
      encode_bytes 9 (last record) ++
      encode_bytes 9 (closing_price record) ++
      encode_bytes 9 (start_of_day_price record) ++
      encode_bytes 17 (total_volume record) ++
      encode_bytes 17 (total_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (opening_price_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (high_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (low_value, bytes) =>
                      match decode_bytes 9 bytes with
                      | None => None
                      | Some (last_value, bytes) =>
                          match decode_bytes 9 bytes with
                          | None => None
                          | Some (closing_price_value, bytes) =>
                              match decode_bytes 9 bytes with
                              | None => None
                              | Some (start_of_day_price_value, bytes) =>
                                  match decode_bytes 17 bytes with
                                  | None => None
                                  | Some (total_volume_value, bytes) =>
                                      match decode_bytes 17 bytes with
                                      | None => None
                                      | Some (total_value_value, bytes) =>
                                          Some ({| symbol := symbol_value; opening_price := opening_price_value; high := high_value; low := low_value; last := last_value; closing_price := closing_price_value; start_of_day_price := start_of_day_price_value; total_volume := total_volume_value; total_value := total_value_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 103.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End InstrumentSummaryMessage.

  Module ClosingPriceMessage.

    (** Transmitted for every instrument whose closing price has been calculated by the trading platform, and again whenever the trading platform recalculates one *)
    Record t := {
      symbol : list byte;
      closing : list byte;
      open_interest : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 15 /\
      Datatypes.length (closing record) = 9 /\
      Datatypes.length (open_interest record) = 8.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (symbol record) ++
      encode_bytes 9 (closing record) ++
      encode_bytes 8 (open_interest record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (closing_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (open_interest_value, bytes) =>
                  Some ({| symbol := symbol_value; closing := closing_value; open_interest := open_interest_value |}, bytes)
              end
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
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClosingPriceMessage.

  Module ProjectedAuctionAuctionOpenProjectedClosePriceMessage.

    (** Transmitted whenever the trading platform calculates a Projected Auction, Auction Open or Projected Close price for the instrument *)
    Record t := {
      symbol : list byte;
      price_flag : list byte;
      price : list byte;
      volume : list byte;
      time_stamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 15 /\
      Datatypes.length (price_flag record) = 1 /\
      Datatypes.length (price record) = 9 /\
      Datatypes.length (volume record) = 17 /\
      Datatypes.length (time_stamp record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (symbol record) ++
      encode_bytes 1 (price_flag record) ++
      encode_bytes 9 (price record) ++
      encode_bytes 17 (volume record) ++
      encode_bytes 20 (time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (price_flag_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_bytes 17 bytes with
                  | None => None
                  | Some (volume_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (time_stamp_value, bytes) =>
                          Some ({| symbol := symbol_value; price_flag := price_flag_value; price := price_value; volume := volume_value; time_stamp := time_stamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 62.
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

  End ProjectedAuctionAuctionOpenProjectedClosePriceMessage.

  Module HighLowLimitModificationMessage.

    (** Transmitted at the beginning of the trading day, and whenever the static High and Low limits for the given instrument change *)
    Record t := {
      symbol : list byte;
      ceiling_price : list byte;
      floor_price : list byte;
      start_of_day_price : list byte;
      accrued_interest : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 15 /\
      Datatypes.length (ceiling_price record) = 9 /\
      Datatypes.length (floor_price record) = 9 /\
      Datatypes.length (start_of_day_price record) = 9 /\
      Datatypes.length (accrued_interest record) = 14.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (symbol record) ++
      encode_bytes 9 (ceiling_price record) ++
      encode_bytes 9 (floor_price record) ++
      encode_bytes 9 (start_of_day_price record) ++
      encode_bytes 14 (accrued_interest record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 9 bytes with
          | None => None
          | Some (ceiling_price_value, bytes) =>
              match decode_bytes 9 bytes with
              | None => None
              | Some (floor_price_value, bytes) =>
                  match decode_bytes 9 bytes with
                  | None => None
                  | Some (start_of_day_price_value, bytes) =>
                      match decode_bytes 14 bytes with
                      | None => None
                      | Some (accrued_interest_value, bytes) =>
                          Some ({| symbol := symbol_value; ceiling_price := ceiling_price_value; floor_price := floor_price_value; start_of_day_price := start_of_day_price_value; accrued_interest := accrued_interest_value |}, bytes)
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

  End HighLowLimitModificationMessage.

  Module InstrumentStateMessage.

    (** Transmitted at the beginning of the trading day, and whenever the instrument changes its trading phase or its status *)
    Record t := {
      symbol : list byte;
      phase_id : list byte;
      instrument_status : list byte;
      halt_suspend_reason : list byte;
      time_stamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 15 /\
      Datatypes.length (phase_id record) = 1 /\
      Datatypes.length (instrument_status record) = 1 /\
      Datatypes.length (halt_suspend_reason record) = 1 /\
      Datatypes.length (time_stamp record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (symbol record) ++
      encode_bytes 1 (phase_id record) ++
      encode_bytes 1 (instrument_status record) ++
      encode_bytes 1 (halt_suspend_reason record) ++
      encode_bytes 20 (time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (phase_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (instrument_status_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (halt_suspend_reason_value, bytes) =>
                      match decode_bytes 20 bytes with
                      | None => None
                      | Some (time_stamp_value, bytes) =>
                          Some ({| symbol := symbol_value; phase_id := phase_id_value; instrument_status := instrument_status_value; halt_suspend_reason := halt_suspend_reason_value; time_stamp := time_stamp_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 38.
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

  End InstrumentStateMessage.

  Module MarketStatusMessage.

    (** Transmitted whenever the market changes its status *)
    Record t := {
      market_id : list byte;
      market_status : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market_id record) = 1 /\
      Datatypes.length (market_status record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market_id record) ++
      encode_bytes 1 (market_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_id_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (market_status_value, bytes) =>
              Some ({| market_id := market_id_value; market_status := market_status_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 2.
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

  End MarketStatusMessage.

  Module OrderMessage.

    (** Transmitted at the beginning of the trading session for an order whose lifetime spans multiple days, when a new order is entered in the trading platform, and when an already placed order is changed. It is not transmitted for Combinations *)
    Record t := {
      symbol : list byte;
      board_id : list byte;
      order_number : list byte;
      order_entry_date : list byte;
      order_status : list byte;
      side : list byte;
      volume : list byte;
      matched_volume : list byte;
      price : list byte;
      original_price_type : list byte;
      order_lifetime : list byte;
      special_conditions : list byte;
      condition_volume : list byte;
      order_release_date : list byte;
      order_release_time : list byte;
      last_order_update_date : list byte;
      order_type : list byte;
      time_stamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 15 /\
      Datatypes.length (board_id record) = 1 /\
      Datatypes.length (order_number record) = 8 /\
      Datatypes.length (order_entry_date record) = 8 /\
      Datatypes.length (order_status record) = 2 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (volume record) = 17 /\
      Datatypes.length (matched_volume record) = 17 /\
      Datatypes.length (price record) = 9 /\
      Datatypes.length (original_price_type record) = 1 /\
      Datatypes.length (order_lifetime record) = 1 /\
      Datatypes.length (special_conditions record) = 1 /\
      Datatypes.length (condition_volume record) = 17 /\
      Datatypes.length (order_release_date record) = 8 /\
      Datatypes.length (order_release_time record) = 12 /\
      Datatypes.length (last_order_update_date record) = 8 /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (time_stamp record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (symbol record) ++
      encode_bytes 1 (board_id record) ++
      encode_bytes 8 (order_number record) ++
      encode_bytes 8 (order_entry_date record) ++
      encode_bytes 2 (order_status record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 17 (volume record) ++
      encode_bytes 17 (matched_volume record) ++
      encode_bytes 9 (price record) ++
      encode_bytes 1 (original_price_type record) ++
      encode_bytes 1 (order_lifetime record) ++
      encode_bytes 1 (special_conditions record) ++
      encode_bytes 17 (condition_volume record) ++
      encode_bytes 8 (order_release_date record) ++
      encode_bytes 12 (order_release_time record) ++
      encode_bytes 8 (last_order_update_date record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 20 (time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (order_number_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (order_entry_date_value, bytes) =>
                      match decode_bytes 2 bytes with
                      | None => None
                      | Some (order_status_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (side_value, bytes) =>
                              match decode_bytes 17 bytes with
                              | None => None
                              | Some (volume_value, bytes) =>
                                  match decode_bytes 17 bytes with
                                  | None => None
                                  | Some (matched_volume_value, bytes) =>
                                      match decode_bytes 9 bytes with
                                      | None => None
                                      | Some (price_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (original_price_type_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (order_lifetime_value, bytes) =>
                                                  match decode_bytes 1 bytes with
                                                  | None => None
                                                  | Some (special_conditions_value, bytes) =>
                                                      match decode_bytes 17 bytes with
                                                      | None => None
                                                      | Some (condition_volume_value, bytes) =>
                                                          match decode_bytes 8 bytes with
                                                          | None => None
                                                          | Some (order_release_date_value, bytes) =>
                                                              match decode_bytes 12 bytes with
                                                              | None => None
                                                              | Some (order_release_time_value, bytes) =>
                                                                  match decode_bytes 8 bytes with
                                                                  | None => None
                                                                  | Some (last_order_update_date_value, bytes) =>
                                                                      match decode_bytes 1 bytes with
                                                                      | None => None
                                                                      | Some (order_type_value, bytes) =>
                                                                          match decode_bytes 20 bytes with
                                                                          | None => None
                                                                          | Some (time_stamp_value, bytes) =>
                                                                              Some ({| symbol := symbol_value; board_id := board_id_value; order_number := order_number_value; order_entry_date := order_entry_date_value; order_status := order_status_value; side := side_value; volume := volume_value; matched_volume := matched_volume_value; price := price_value; original_price_type := original_price_type_value; order_lifetime := order_lifetime_value; special_conditions := special_conditions_value; condition_volume := condition_volume_value; order_release_date := order_release_date_value; order_release_time := order_release_time_value; last_order_update_date := last_order_update_date_value; order_type := order_type_value; time_stamp := time_stamp_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 147.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderMessage.

  Module CancelledOrderMessage.

    (** Transmitted whenever an order is cancelled. It is not transmitted for Combinations *)
    Record t := {
      symbol : list byte;
      board_id : list byte;
      order_number : list byte;
      order_entry_date : list byte;
      side : list byte;
      volume : list byte;
      matched_volume : list byte;
      price : list byte;
      original_price_type : list byte;
      order_lifetime : list byte;
      special_conditions : list byte;
      condition_volume : list byte;
      order_type : list byte;
      time_stamp : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (symbol record) = 15 /\
      Datatypes.length (board_id record) = 1 /\
      Datatypes.length (order_number record) = 8 /\
      Datatypes.length (order_entry_date record) = 8 /\
      Datatypes.length (side record) = 1 /\
      Datatypes.length (volume record) = 17 /\
      Datatypes.length (matched_volume record) = 17 /\
      Datatypes.length (price record) = 9 /\
      Datatypes.length (original_price_type record) = 1 /\
      Datatypes.length (order_lifetime record) = 1 /\
      Datatypes.length (special_conditions record) = 1 /\
      Datatypes.length (condition_volume record) = 17 /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (time_stamp record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 15 (symbol record) ++
      encode_bytes 1 (board_id record) ++
      encode_bytes 8 (order_number record) ++
      encode_bytes 8 (order_entry_date record) ++
      encode_bytes 1 (side record) ++
      encode_bytes 17 (volume record) ++
      encode_bytes 17 (matched_volume record) ++
      encode_bytes 9 (price record) ++
      encode_bytes 1 (original_price_type record) ++
      encode_bytes 1 (order_lifetime record) ++
      encode_bytes 1 (special_conditions record) ++
      encode_bytes 17 (condition_volume record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 20 (time_stamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 15 bytes with
      | None => None
      | Some (symbol_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (board_id_value, bytes) =>
              match decode_bytes 8 bytes with
              | None => None
              | Some (order_number_value, bytes) =>
                  match decode_bytes 8 bytes with
                  | None => None
                  | Some (order_entry_date_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (side_value, bytes) =>
                          match decode_bytes 17 bytes with
                          | None => None
                          | Some (volume_value, bytes) =>
                              match decode_bytes 17 bytes with
                              | None => None
                              | Some (matched_volume_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (price_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (original_price_type_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (order_lifetime_value, bytes) =>
                                              match decode_bytes 1 bytes with
                                              | None => None
                                              | Some (special_conditions_value, bytes) =>
                                                  match decode_bytes 17 bytes with
                                                  | None => None
                                                  | Some (condition_volume_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (order_type_value, bytes) =>
                                                          match decode_bytes 20 bytes with
                                                          | None => None
                                                          | Some (time_stamp_value, bytes) =>
                                                              Some ({| symbol := symbol_value; board_id := board_id_value; order_number := order_number_value; order_entry_date := order_entry_date_value; side := side_value; volume := volume_value; matched_volume := matched_volume_value; price := price_value; original_price_type := original_price_type_value; order_lifetime := order_lifetime_value; special_conditions := special_conditions_value; condition_volume := condition_volume_value; order_type := order_type_value; time_stamp := time_stamp_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 117.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
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
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CancelledOrderMessage.

End AthexSecuritiesRealTimeV52.
