From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Chicago Board Options Exchange Multicast Top Of Book

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
  *)

Module CxaEquitiesMulticastTopOfBookV1010.

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

  Module UnitClearMessage.

    (** Instructs feed recipients to clear all data for the CXA book in the unit specified in the Sequenced Unit Header. Distributed in rare recovery events such as a datacentre fail-over. *)
    Record t := {
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (reserved_4_value, bytes) =>
          Some ({| reserved_4 := reserved_4_value |}, bytes)
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

  End UnitClearMessage.

  Module TradingStatusMessage.

    (** Indicates the current trading status of a security. A Trading Status message will be sent whenever trading status changes for a security. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      trading_status : list byte;
      market_id_code : list byte;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (trading_status record) = 1 /\
      Datatypes.length (market_id_code record) = 4 /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (trading_status record) ++
      encode_bytes 4 (market_id_code record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_status_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (market_id_code_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol := symbol_value; trading_status := trading_status_value; market_id_code := market_id_code_value; reserved_1 := reserved_1_value |}, bytes)
                      end
                  end
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

  End TradingStatusMessage.

  Module SingleSideUpdateMessage.

    (** Provides an updated price and size for a single side of a Symbol. The side is denoted by the Side field. One Single Side Update message may reflect one or more updates to the inside book that were processed at the same time but will only be done so in a way that can be arbitrated between A/B feeds. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      side : list byte;
      price : N;
      quantity : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (side record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 4)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (side record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (quantity record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (quantity_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| timestamp := timestamp_value; symbol := symbol_value; side := side_value; price := price_value; quantity := quantity_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideUpdateMessage.

  Module TwoSideUpdateMessage.

    (** Provides an updated price and size for both sides of a Symbol. One Two Side Update message may reflect one or more updates to the inside book that were processed at the same time but will only be done so in a way that can be arbitrated between A/B feeds. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      bid_price : N;
      bid_quantity : N;
      reserved_1 : N;
      ask_price : N;
      ask_quantity : N;
      second_reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (bid_quantity record < 256 ^ N.of_nat 4)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (ask_price record < 256 ^ N.of_nat 8)%N /\
      (ask_quantity record < 256 ^ N.of_nat 4)%N /\
      (second_reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_uint 8 (bid_price record) ++
      encode_uint 4 (bid_quantity record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 8 (ask_price record) ++
      encode_uint 4 (ask_quantity record) ++
      encode_uint 1 (second_reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (bid_quantity_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (reserved_1_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (ask_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (ask_quantity_value, bytes) =>
                                  match decode_uint 1 bytes with
                                  | None => None
                                  | Some (second_reserved_1_value, bytes) =>
                                      Some ({| timestamp := timestamp_value; symbol := symbol_value; bid_price := bid_price_value; bid_quantity := bid_quantity_value; reserved_1 := reserved_1_value; ask_price := ask_price_value; ask_quantity := ask_quantity_value; second_reserved_1 := second_reserved_1_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TwoSideUpdateMessage.

  Module CalculatedValueMessage.

    (** Sent when CXA calculates market values for a specified symbol or when a calculated market value is reported to CXA. The specified symbol may not trade on CXA, but instead could represent index or iNAV values reported to CXA from third parties as indicated by the Value Category field. The index values will be reported on each of the unitised CXA TOP feeds and are not specific to an individual unit. Calculated Value messages will be included in a spin response. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      value_category : list byte;
      value : N;
      value_timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (value_category record) = 1 /\
      (value record < 256 ^ N.of_nat 8)%N /\
      (value_timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (value_category record) ++
      encode_uint 8 (value record) ++
      encode_uint 8 (value_timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (value_category_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (value_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (value_timestamp_value, bytes) =>
                          Some ({| timestamp := timestamp_value; symbol := symbol_value; value_category := value_category_value; value := value_value; value_timestamp := value_timestamp_value |}, bytes)
                      end
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

  End CalculatedValueMessage.

  Module EndOfSessionMessage.

    (** Sent for each unit when the unit shuts down. No more sequenced messages will be delivered for this unit, but heartbeats from the unit may be received. *)
    Record t := {
      reserved_4 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_4 record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (reserved_4 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (reserved_4_value, bytes) =>
          Some ({| reserved_4 := reserved_4_value |}, bytes)
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

  Module AuctionUpdateMessage.

    (** Sent during Pre-Open and Pre-Close trading states when a symbol has an order update which relates to an overlapping order book (where the best bid price is greater than or equal to the best ask price). Includes the potential number of shares and the indicative auction price if the symbol were to undergo an auction now. Only sent if there are updates to the Buy Shares, Sell Shares, or Indicative Price fields. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      auction_type : list byte;
      buy_shares : N;
      sell_shares : N;
      indicative_price : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (auction_type record) = 1 /\
      (buy_shares record < 256 ^ N.of_nat 4)%N /\
      (sell_shares record < 256 ^ N.of_nat 4)%N /\
      (indicative_price record < 256 ^ N.of_nat 8)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 4 (buy_shares record) ++
      encode_uint 4 (sell_shares record) ++
      encode_uint 8 (indicative_price record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (buy_shares_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (sell_shares_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (indicative_price_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reserved_1_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; symbol := symbol_value; auction_type := auction_type_value; buy_shares := buy_shares_value; sell_shares := sell_shares_value; indicative_price := indicative_price_value; reserved_1 := reserved_1_value |}, bytes)
                              end
                          end
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

  End AuctionUpdateMessage.

  Module AuctionSummaryMessage.

    (** Sent at the completion of the Auction per symbol and includes the Auction Price and Shares traded. If there is no overlapping order book at the time of the auction, no auction trades will result, however the Auction Summary message will still be disseminated and contain zeroes in the Price and Shares fields. *)
    Record t := {
      timestamp : N;
      symbol : list byte;
      auction_type : list byte;
      price : N;
      shares : N;
      reserved_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (symbol record) = 6 /\
      Datatypes.length (auction_type record) = 1 /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (shares record < 256 ^ N.of_nat 4)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (timestamp record) ++
      encode_bytes 6 (symbol record) ++
      encode_bytes 1 (auction_type record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (shares record) ++
      encode_uint 1 (reserved_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 6 bytes with
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
                      | Some (shares_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (reserved_1_value, bytes) =>
                              Some ({| timestamp := timestamp_value; symbol := symbol_value; auction_type := auction_type_value; price := price_value; shares := shares_value; reserved_1 := reserved_1_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 28.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AuctionSummaryMessage.

End CxaEquitiesMulticastTopOfBookV1010.
