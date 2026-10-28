From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Texas Stock Exchange BALE Top-of-Book Market Data Feed

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
      - a field read in bits
  *)

Module TxseEquitiesBaleV10.

  Module UdpHeader.

    (** Rake Udp packet header *)
    Record t := {
      session : N;
      sequence : N;
      message_count : N;
      packet_type : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session record < 256 ^ N.of_nat 8)%N /\
      (sequence record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N /\
      (packet_type record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (session record) ++
      encode_uint 8 (sequence record) ++
      encode_uint 2 (message_count record) ++
      encode_uint 1 (packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (packet_type_value, bytes) =>
                      Some ({| session := session_value; sequence := sequence_value; message_count := message_count_value; packet_type := packet_type_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 19.
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

  End UdpHeader.

  Module TradeMessage.

    (** An execution report for a single fill event in the order book. Quantity is the number of shares in this execution. An aggressive order that sweeps multiple resting orders produces one Trade per resting order filled. *)
    Record t := {
      transact_time : N;
      symbol_id : N;
      price : N;
      qty : N;
      trade_through_exemption_reason : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (qty record < 256 ^ N.of_nat 4)%N /\
      (trade_through_exemption_reason record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 2 (symbol_id record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (qty record) ++
      encode_uint 1 (trade_through_exemption_reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (qty_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (trade_through_exemption_reason_value, bytes) =>
                          Some ({| transact_time := transact_time_value; symbol_id := symbol_id_value; price := price_value; qty := qty_value; trade_through_exemption_reason := trade_through_exemption_reason_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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

  End TradeMessage.

  Module TopOfBookMessage.

    (** Current best bid and offer for a symbol. The BBO is the most aggressive price at which cumulative displayed liquidity reaches a round lot. Quantity is the total displayed shares at the BBO price combined with any displayed shares at more aggressive prices on that side. Price and quantity are zero when cumulative displayed liquidity does not reach a round lot. A TopOfBook is published whenever a depth change occurs at or inside the current BBO on the affected side. A TopOfBook may be published with values identical to the previous one if the net result for the BBO happens to be unchanged after a relevant quantity change. When an execution causes both Trade and TopOfBook messages, all Trade messages from that execution event are delivered before the TopOfBook that reflects the resulting depth change. *)
    Record t := {
      transact_time : N;
      symbol_id : N;
      bid_price : N;
      bid_qty : N;
      ask_price : N;
      ask_qty : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (bid_price record < 256 ^ N.of_nat 8)%N /\
      (bid_qty record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 8)%N /\
      (ask_qty record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 2 (symbol_id record) ++
      encode_uint 8 (bid_price record) ++
      encode_uint 4 (bid_qty record) ++
      encode_uint 8 (ask_price record) ++
      encode_uint 4 (ask_qty record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (bid_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (bid_qty_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (ask_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (ask_qty_value, bytes) =>
                              Some ({| transact_time := transact_time_value; symbol_id := symbol_id_value; bid_price := bid_price_value; bid_qty := bid_qty_value; ask_price := ask_price_value; ask_qty := ask_qty_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 34.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TopOfBookMessage.

  Module AuctionPreambleMessage.

    (** Published every 5 seconds during the Accumulation Period to indicate projected auction size. Reports the matched volume and excess side that would result if the auction crossed at that moment, considering only Auction-Only orders; the Continuous Book is excluded. Emitted for OPENING and CLOSING auction types only. Not emitted for HALT or IPO auctions, which proceed directly to the Band Window phase at onset (see AuctionBandWindow). *)
    Record t := {
      transact_time : N;
      symbol_id : N;
      auction_type : N;
      auction_start : N;
      matched_shares : N;
      excess_auction_side : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (auction_type record < 256 ^ N.of_nat 1)%N /\
      (auction_start record < 256 ^ N.of_nat 8)%N /\
      (matched_shares record < 256 ^ N.of_nat 4)%N /\
      (excess_auction_side record < 256 ^ N.of_nat 1)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 2 (symbol_id record) ++
      encode_uint 1 (auction_type record) ++
      encode_uint 8 (auction_start record) ++
      encode_uint 4 (matched_shares record) ++
      encode_uint 1 (excess_auction_side record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (auction_start_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (matched_shares_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (excess_auction_side_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (reserved_8_value, bytes) =>
                                  Some ({| transact_time := transact_time_value; symbol_id := symbol_id_value; auction_type := auction_type_value; auction_start := auction_start_value; matched_shares := matched_shares_value; excess_auction_side := excess_auction_side_value; reserved_8 := reserved_8_value |}, bytes)
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
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 bound_6]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AuctionPreambleMessage.

  Module AuctionBandWindowMessage.

    (** Published every 5 seconds during the Band Window to report Auction-Only volume positioned at each Participation Band boundary. The Participation Band is a volatility-based price range; its derivation methodology is described in the Participation Bands specification. Auction-Only orders entered during the Band Window that are priced outside the band have their price adjusted to the nearest boundary. The Continuous Book is excluded. Volume counting at boundaries: a limit order is counted at each boundary price at which it would be eligible to execute; a market order is counted at both boundaries. Example: a limit buy at $10.05 counts at the lower boundary if lower = $10.05, but not at the upper boundary if upper = $10.10. *)
    Record t := {
      transact_time : N;
      symbol_id : N;
      auction_type : N;
      auction_start : N;
      extension_cycle_count : N;
      lower_participation_band : N;
      buy_shares_at_lower : N;
      sell_shares_at_lower : N;
      upper_participation_band : N;
      buy_shares_at_upper : N;
      sell_shares_at_upper : N;
      reserved_8 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (auction_type record < 256 ^ N.of_nat 1)%N /\
      (auction_start record < 256 ^ N.of_nat 8)%N /\
      (extension_cycle_count record < 256 ^ N.of_nat 1)%N /\
      (lower_participation_band record < 256 ^ N.of_nat 8)%N /\
      (buy_shares_at_lower record < 256 ^ N.of_nat 4)%N /\
      (sell_shares_at_lower record < 256 ^ N.of_nat 4)%N /\
      (upper_participation_band record < 256 ^ N.of_nat 8)%N /\
      (buy_shares_at_upper record < 256 ^ N.of_nat 4)%N /\
      (sell_shares_at_upper record < 256 ^ N.of_nat 4)%N /\
      (reserved_8 record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 2 (symbol_id record) ++
      encode_uint 1 (auction_type record) ++
      encode_uint 8 (auction_start record) ++
      encode_uint 1 (extension_cycle_count record) ++
      encode_uint 8 (lower_participation_band record) ++
      encode_uint 4 (buy_shares_at_lower record) ++
      encode_uint 4 (sell_shares_at_lower record) ++
      encode_uint 8 (upper_participation_band record) ++
      encode_uint 4 (buy_shares_at_upper record) ++
      encode_uint 4 (sell_shares_at_upper record) ++
      encode_uint 8 (reserved_8 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (auction_start_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (extension_cycle_count_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (lower_participation_band_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (buy_shares_at_lower_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (sell_shares_at_lower_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (upper_participation_band_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (buy_shares_at_upper_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (sell_shares_at_upper_value, bytes) =>
                                                  match decode_uint 8 bytes with
                                                  | None => None
                                                  | Some (reserved_8_value, bytes) =>
                                                      Some ({| transact_time := transact_time_value; symbol_id := symbol_id_value; auction_type := auction_type_value; auction_start := auction_start_value; extension_cycle_count := extension_cycle_count_value; lower_participation_band := lower_participation_band_value; buy_shares_at_lower := buy_shares_at_lower_value; sell_shares_at_lower := sell_shares_at_lower_value; upper_participation_band := upper_participation_band_value; buy_shares_at_upper := buy_shares_at_upper_value; sell_shares_at_upper := sell_shares_at_upper_value; reserved_8 := reserved_8_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 60.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 bound_11]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AuctionBandWindowMessage.

  Module AuctionPrintMessage.

    (** Summary of an auction cross. Emitted before any per-order auction execution messages for the same cross. Universal lifecycle terminator — emitted for every auction. Encoding: (a) matchedShares > 0 with a valid auctionPrice indicates a normal cross; (b) matchedShares = 0 with a valid auctionPrice indicates a zero-share completion (e.g., halt-into-close default or demand failure); (c) matchedShares = 0 with auctionPrice = CANCELED_SENTINEL indicates a canceled auction. Where the feed publishes per-order auction executions, those executions share this message's execId. *)
    Record t := {
      transact_time : N;
      symbol_id : N;
      auction_type : N;
      auction_price : N;
      matched_shares : N;
      exec_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (transact_time record < 256 ^ N.of_nat 8)%N /\
      (symbol_id record < 256 ^ N.of_nat 2)%N /\
      (auction_type record < 256 ^ N.of_nat 1)%N /\
      (auction_price record < 256 ^ N.of_nat 8)%N /\
      (matched_shares record < 256 ^ N.of_nat 4)%N /\
      (exec_id record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (transact_time record) ++
      encode_uint 2 (symbol_id record) ++
      encode_uint 1 (auction_type record) ++
      encode_uint 8 (auction_price record) ++
      encode_uint 4 (matched_shares record) ++
      encode_uint 8 (exec_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (transact_time_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (symbol_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (auction_type_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (auction_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (matched_shares_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (exec_id_value, bytes) =>
                              Some ({| transact_time := transact_time_value; symbol_id := symbol_id_value; auction_type := auction_type_value; auction_price := auction_price_value; matched_shares := matched_shares_value; exec_id := exec_id_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 31.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End AuctionPrintMessage.

End TxseEquitiesBaleV10.
