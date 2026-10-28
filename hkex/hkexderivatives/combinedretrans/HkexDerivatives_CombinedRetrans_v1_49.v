From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Hong Kong Exchanges and Clearing Orion Market Data Derivatives Combined Retransmission

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
      - a Reassemble rule
      - a run counted by a field
      - a field read in bits
  *)

Module HkexDerivativesCombinedRetransV149.

  Module PacketHeader.

    (** Omd packet header (byte-identical to the Udp form; SeqNum and SendTime set to 0 on Tcp per §3.5) *)
    Record t := {
      pkt_size : N;
      msg_count : N;
      compression_mode : N;
      seq_num : N;
      send_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (pkt_size record < 256 ^ N.of_nat 2)%N /\
      (msg_count record < 256 ^ N.of_nat 1)%N /\
      (compression_mode record < 256 ^ N.of_nat 1)%N /\
      (seq_num record < 256 ^ N.of_nat 4)%N /\
      (send_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (pkt_size record) ++
      encode_uint 1 (msg_count record) ++
      encode_uint 1 (compression_mode record) ++
      encode_uint 4 (seq_num record) ++
      encode_uint 8 (send_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (pkt_size_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (msg_count_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (compression_mode_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (seq_num_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (send_time_value, bytes) =>
                          Some ({| pkt_size := pkt_size_value; msg_count := msg_count_value; compression_mode := compression_mode_value; seq_num := seq_num_value; send_time := send_time_value |}, bytes)
                      end
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

  End PacketHeader.

  Module MsgHeader.

    (** Omd message header *)
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

  End MsgHeader.

  Module CalculatedOpeningPriceMessage.

    (** The Calculated Opening Price (COP) message indicates an instrument's theoretical opening price during the pre-opening phases of the market prior to an auction *)
    Record t := {
      orderbook_id : N;
      calculated_opening_price : N;
      filler_4 : N;
      quantity : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (calculated_opening_price record < 256 ^ N.of_nat 4)%N /\
      (filler_4 record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 4 (calculated_opening_price record) ++
      encode_uint 4 (filler_4 record) ++
      encode_uint 8 (quantity record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (calculated_opening_price_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (filler_4_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      Some ({| orderbook_id := orderbook_id_value; calculated_opening_price := calculated_opening_price_value; filler_4 := filler_4_value; quantity := quantity_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End CalculatedOpeningPriceMessage.

  Module SequenceReset.

    (** The Sequence Reset message is sent on each multicast channel at start of day *)
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

  End SequenceReset.

  Module DisasterRecoverySignalMessage.

    (** The Disaster Recovery Signal message is sent on a dedicated multicast channel whenever a site failover scenario is triggered *)
    Record t := {
      dr_status : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (dr_status record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (dr_status record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (dr_status_value, bytes) =>
          Some ({| dr_status := dr_status_value |}, bytes)
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

  End DisasterRecoverySignalMessage.

  Module ImpliedVolatilityMessage.

    (** Contains implied volitility *)
    Record t := {
      orderbook_id : N;
      implied_volatility : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (implied_volatility record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 4 (implied_volatility record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (implied_volatility_value, bytes) =>
              Some ({| orderbook_id := orderbook_id_value; implied_volatility := implied_volatility_value |}, bytes)
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

  End ImpliedVolatilityMessage.

  Module OpenInterestMessage.

    (** Issued to show the Previous Day settlement price and open interest *)
    Record t := {
      day_indicator : N;
      filler_6 : N;
      orderbook_id : N;
      settlement : N;
      deal_count : N;
      gross_oi : N;
      net_oi : N;
      turnover : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (day_indicator record < 256 ^ N.of_nat 2)%N /\
      (filler_6 record < 256 ^ N.of_nat 6)%N /\
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (settlement record < 256 ^ N.of_nat 4)%N /\
      (deal_count record < 256 ^ N.of_nat 4)%N /\
      (gross_oi record < 256 ^ N.of_nat 4)%N /\
      (net_oi record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (day_indicator record) ++
      encode_uint 6 (filler_6 record) ++
      encode_uint 4 (orderbook_id record) ++
      encode_uint 4 (settlement record) ++
      encode_uint 4 (deal_count record) ++
      encode_uint 4 (gross_oi record) ++
      encode_uint 4 (net_oi record) ++
      encode_uint 8 (turnover record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (day_indicator_value, bytes) =>
          match decode_uint 6 bytes with
          | None => None
          | Some (filler_6_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_id_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (settlement_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (deal_count_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (gross_oi_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (net_oi_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (turnover_value, bytes) =>
                                      Some ({| day_indicator := day_indicator_value; filler_6 := filler_6_value; orderbook_id := orderbook_id_value; settlement := settlement_value; deal_count := deal_count_value; gross_oi := gross_oi_value; net_oi := net_oi_value; turnover := turnover_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OpenInterestMessage.

  Module DeleteOrderMessage.

    (** The Delete Order message is generated when an existing order identified by the OrderBookID, OrderID and Side is deleted *)
    Record t := {
      orderbook_id : N;
      order_id : N;
      side : N;
      filler_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (order_id record < 256 ^ N.of_nat 8)%N /\
      (side record < 256 ^ N.of_nat 1)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 8 (order_id record) ++
      encode_uint 1 (side record) ++
      encode_uint 1 (filler_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_id_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (side_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (filler_1_value, bytes) =>
                      Some ({| orderbook_id := orderbook_id_value; order_id := order_id_value; side := side_value; filler_1 := filler_1_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 14.
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

  End DeleteOrderMessage.

  Module OrderbookClearMessage.

    (** The Orderbook Clear message is used to inform clients that all existing orders should be removed from both the bid and ask sides of the specified orderbook *)
    Record t := {
      orderbook_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          Some ({| orderbook_id := orderbook_id_value |}, bytes)
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

  End OrderbookClearMessage.

  Module QuoteRequest.

    (** The Quote Request message is generated whenever market participants request a new quotation *)
    Record t := {
      orderbook_id : N;
      number_of_lots : N;
      bid_ask_flag : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (number_of_lots record < 256 ^ N.of_nat 4)%N /\
      (bid_ask_flag record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 4 (number_of_lots record) ++
      encode_uint 1 (bid_ask_flag record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (number_of_lots_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (bid_ask_flag_value, bytes) =>
                  match decode_uint 3 bytes with
                  | None => None
                  | Some (filler_3_value, bytes) =>
                      Some ({| orderbook_id := orderbook_id_value; number_of_lots := number_of_lots_value; bid_ask_flag := bid_ask_flag_value; filler_3 := filler_3_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End QuoteRequest.

  Module CommodityDefinitionMessage.

    (** Describes individual commodities available from the OMD-D system *)
    Record t := {
      commodity_code : N;
      decimal_in_underlying_price : N;
      isin_code : list byte;
      base_currency : list byte;
      underlying_price_unit : N;
      commodity_name : list byte;
      nominal_value : N;
      underlying_code : list byte;
      underlying_type : N;
      effective_tomorrow : N;
      commodity_id : list byte;
      filler_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (commodity_code record < 256 ^ N.of_nat 2)%N /\
      (decimal_in_underlying_price record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (isin_code record) = 12 /\
      Datatypes.length (base_currency record) = 3 /\
      (underlying_price_unit record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (commodity_name record) = 32 /\
      (nominal_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (underlying_code record) = 20 /\
      (underlying_type record < 256 ^ N.of_nat 1)%N /\
      (effective_tomorrow record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (commodity_id record) = 6 /\
      (filler_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (commodity_code record) ++
      encode_uint 2 (decimal_in_underlying_price record) ++
      encode_bytes 12 (isin_code record) ++
      encode_bytes 3 (base_currency record) ++
      encode_uint 1 (underlying_price_unit record) ++
      encode_bytes 32 (commodity_name record) ++
      encode_uint 8 (nominal_value record) ++
      encode_bytes 20 (underlying_code record) ++
      encode_uint 1 (underlying_type record) ++
      encode_uint 1 (effective_tomorrow record) ++
      encode_bytes 6 (commodity_id record) ++
      encode_uint 2 (filler_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (commodity_code_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (decimal_in_underlying_price_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_code_value, bytes) =>
                  match decode_bytes 3 bytes with
                  | None => None
                  | Some (base_currency_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (underlying_price_unit_value, bytes) =>
                          match decode_bytes 32 bytes with
                          | None => None
                          | Some (commodity_name_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (nominal_value_value, bytes) =>
                                  match decode_bytes 20 bytes with
                                  | None => None
                                  | Some (underlying_code_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (underlying_type_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (effective_tomorrow_value, bytes) =>
                                              match decode_bytes 6 bytes with
                                              | None => None
                                              | Some (commodity_id_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (filler_2_value, bytes) =>
                                                      Some ({| commodity_code := commodity_code_value; decimal_in_underlying_price := decimal_in_underlying_price_value; isin_code := isin_code_value; base_currency := base_currency_value; underlying_price_unit := underlying_price_unit_value; commodity_name := commodity_name_value; nominal_value := nominal_value_value; underlying_code := underlying_code_value; underlying_type := underlying_type_value; effective_tomorrow := effective_tomorrow_value; commodity_id := commodity_id_value; filler_2 := filler_2_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 90.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
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
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CommodityDefinitionMessage.

  Module ClassDefinitionMessage.

    (** Describes individual instrument classes available from the OMD-D system *)
    Record t := {
      country : N;
      market : N;
      instrument_group : N;
      modifier : N;
      commodity_code : N;
      filler_2 : N;
      price_quotation_factor : N;
      contract_size : N;
      decimal_in_strike_price : N;
      decimal_in_contract_size : N;
      decimal_in_premium : N;
      ranking_type : N;
      tradable : N;
      premium_unit_4_price : N;
      base_currency : list byte;
      instrument_class_id : list byte;
      instrument_class_name : list byte;
      is_fractions : list byte;
      settlement_currency_id : list byte;
      effective_tomorrow : N;
      tick_step_size : N;
      filler_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (country record < 256 ^ N.of_nat 1)%N /\
      (market record < 256 ^ N.of_nat 1)%N /\
      (instrument_group record < 256 ^ N.of_nat 1)%N /\
      (modifier record < 256 ^ N.of_nat 1)%N /\
      (commodity_code record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      (price_quotation_factor record < 256 ^ N.of_nat 4)%N /\
      (contract_size record < 256 ^ N.of_nat 4)%N /\
      (decimal_in_strike_price record < 256 ^ N.of_nat 2)%N /\
      (decimal_in_contract_size record < 256 ^ N.of_nat 2)%N /\
      (decimal_in_premium record < 256 ^ N.of_nat 2)%N /\
      (ranking_type record < 256 ^ N.of_nat 2)%N /\
      (tradable record < 256 ^ N.of_nat 1)%N /\
      (premium_unit_4_price record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (base_currency record) = 3 /\
      Datatypes.length (instrument_class_id record) = 14 /\
      Datatypes.length (instrument_class_name record) = 32 /\
      Datatypes.length (is_fractions record) = 1 /\
      Datatypes.length (settlement_currency_id record) = 32 /\
      (effective_tomorrow record < 256 ^ N.of_nat 1)%N /\
      (tick_step_size record < 256 ^ N.of_nat 4)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (country record) ++
      encode_uint 1 (market record) ++
      encode_uint 1 (instrument_group record) ++
      encode_uint 1 (modifier record) ++
      encode_uint 2 (commodity_code record) ++
      encode_uint 2 (filler_2 record) ++
      encode_uint 4 (price_quotation_factor record) ++
      encode_uint 4 (contract_size record) ++
      encode_uint 2 (decimal_in_strike_price record) ++
      encode_uint 2 (decimal_in_contract_size record) ++
      encode_uint 2 (decimal_in_premium record) ++
      encode_uint 2 (ranking_type record) ++
      encode_uint 1 (tradable record) ++
      encode_uint 1 (premium_unit_4_price record) ++
      encode_bytes 3 (base_currency record) ++
      encode_bytes 14 (instrument_class_id record) ++
      encode_bytes 32 (instrument_class_name record) ++
      encode_bytes 1 (is_fractions record) ++
      encode_bytes 32 (settlement_currency_id record) ++
      encode_uint 1 (effective_tomorrow record) ++
      encode_uint 4 (tick_step_size record) ++
      encode_uint 1 (filler_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (country_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (market_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (instrument_group_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (modifier_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (commodity_code_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (filler_2_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_quotation_factor_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (contract_size_value, bytes) =>
                                      match decode_uint 2 bytes with
                                      | None => None
                                      | Some (decimal_in_strike_price_value, bytes) =>
                                          match decode_uint 2 bytes with
                                          | None => None
                                          | Some (decimal_in_contract_size_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (decimal_in_premium_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (ranking_type_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (tradable_value, bytes) =>
                                                          match decode_uint 1 bytes with
                                                          | None => None
                                                          | Some (premium_unit_4_price_value, bytes) =>
                                                              match decode_bytes 3 bytes with
                                                              | None => None
                                                              | Some (base_currency_value, bytes) =>
                                                                  match decode_bytes 14 bytes with
                                                                  | None => None
                                                                  | Some (instrument_class_id_value, bytes) =>
                                                                      match decode_bytes 32 bytes with
                                                                      | None => None
                                                                      | Some (instrument_class_name_value, bytes) =>
                                                                          match decode_bytes 1 bytes with
                                                                          | None => None
                                                                          | Some (is_fractions_value, bytes) =>
                                                                              match decode_bytes 32 bytes with
                                                                              | None => None
                                                                              | Some (settlement_currency_id_value, bytes) =>
                                                                                  match decode_uint 1 bytes with
                                                                                  | None => None
                                                                                  | Some (effective_tomorrow_value, bytes) =>
                                                                                      match decode_uint 4 bytes with
                                                                                      | None => None
                                                                                      | Some (tick_step_size_value, bytes) =>
                                                                                          match decode_uint 1 bytes with
                                                                                          | None => None
                                                                                          | Some (filler_1_value, bytes) =>
                                                                                              Some ({| country := country_value; market := market_value; instrument_group := instrument_group_value; modifier := modifier_value; commodity_code := commodity_code_value; filler_2 := filler_2_value; price_quotation_factor := price_quotation_factor_value; contract_size := contract_size_value; decimal_in_strike_price := decimal_in_strike_price_value; decimal_in_contract_size := decimal_in_contract_size_value; decimal_in_premium := decimal_in_premium_value; ranking_type := ranking_type_value; tradable := tradable_value; premium_unit_4_price := premium_unit_4_price_value; base_currency := base_currency_value; instrument_class_id := instrument_class_id_value; instrument_class_name := instrument_class_name_value; is_fractions := is_fractions_value; settlement_currency_id := settlement_currency_id_value; effective_tomorrow := effective_tomorrow_value; tick_step_size := tick_step_size_value; filler_1 := filler_1_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 114.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 [bound_18 [bound_19 [bound_20 bound_21]]]]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_bytes by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      rewrite decode_encode_uint by exact bound_19.
      rewrite decode_encode_uint by exact bound_20.
      rewrite decode_encode_uint by exact bound_21.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ClassDefinitionMessage.

  Module SeriesDefinitionBaseMessage.

    (** Describes basic series information *)
    Record t := {
      orderbook_id : N;
      symbol : list byte;
      financial_product : N;
      number_of_decimals_price : N;
      number_of_legs : N;
      strike_price : N;
      expiration_date : list byte;
      decimal_in_strike_price : N;
      put_or_call : N;
      filler_1 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 32 /\
      (financial_product record < 256 ^ N.of_nat 1)%N /\
      (number_of_decimals_price record < 256 ^ N.of_nat 2)%N /\
      (number_of_legs record < 256 ^ N.of_nat 1)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (expiration_date record) = 8 /\
      (decimal_in_strike_price record < 256 ^ N.of_nat 2)%N /\
      (put_or_call record < 256 ^ N.of_nat 1)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_bytes 32 (symbol record) ++
      encode_uint 1 (financial_product record) ++
      encode_uint 2 (number_of_decimals_price record) ++
      encode_uint 1 (number_of_legs record) ++
      encode_uint 4 (strike_price record) ++
      encode_bytes 8 (expiration_date record) ++
      encode_uint 2 (decimal_in_strike_price record) ++
      encode_uint 1 (put_or_call record) ++
      encode_uint 1 (filler_1 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_bytes 32 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (financial_product_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (number_of_decimals_price_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (number_of_legs_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (strike_price_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (expiration_date_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (decimal_in_strike_price_value, bytes) =>
                                      match decode_uint 1 bytes with
                                      | None => None
                                      | Some (put_or_call_value, bytes) =>
                                          match decode_uint 1 bytes with
                                          | None => None
                                          | Some (filler_1_value, bytes) =>
                                              Some ({| orderbook_id := orderbook_id_value; symbol := symbol_value; financial_product := financial_product_value; number_of_decimals_price := number_of_decimals_price_value; number_of_legs := number_of_legs_value; strike_price := strike_price_value; expiration_date := expiration_date_value; decimal_in_strike_price := decimal_in_strike_price_value; put_or_call := put_or_call_value; filler_1 := filler_1_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesDefinitionBaseMessage.

  Module SeriesDefinitionExtendedMessage.

    (** Describes series static data *)
    Record t := {
      orderbook_id : N;
      symbol : list byte;
      country : N;
      market : N;
      instrument_group : N;
      modifier : N;
      commodity_code : N;
      expiry_date : N;
      strike_price : N;
      contract_size_extended : N;
      isin_code : list byte;
      series_status : N;
      effective_tomorrow : N;
      price_quotation_factor : N;
      price_method : N;
      filler_1 : N;
      effective_exp_date : list byte;
      date_time_last_trading : N;
      date_time_first_trading : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (symbol record) = 32 /\
      (country record < 256 ^ N.of_nat 1)%N /\
      (market record < 256 ^ N.of_nat 1)%N /\
      (instrument_group record < 256 ^ N.of_nat 1)%N /\
      (modifier record < 256 ^ N.of_nat 1)%N /\
      (commodity_code record < 256 ^ N.of_nat 2)%N /\
      (expiry_date record < 256 ^ N.of_nat 2)%N /\
      (strike_price record < 256 ^ N.of_nat 4)%N /\
      (contract_size_extended record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (isin_code record) = 12 /\
      (series_status record < 256 ^ N.of_nat 1)%N /\
      (effective_tomorrow record < 256 ^ N.of_nat 1)%N /\
      (price_quotation_factor record < 256 ^ N.of_nat 4)%N /\
      (price_method record < 256 ^ N.of_nat 1)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (effective_exp_date record) = 8 /\
      (date_time_last_trading record < 256 ^ N.of_nat 8)%N /\
      (date_time_first_trading record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_bytes 32 (symbol record) ++
      encode_uint 1 (country record) ++
      encode_uint 1 (market record) ++
      encode_uint 1 (instrument_group record) ++
      encode_uint 1 (modifier record) ++
      encode_uint 2 (commodity_code record) ++
      encode_uint 2 (expiry_date record) ++
      encode_uint 4 (strike_price record) ++
      encode_uint 8 (contract_size_extended record) ++
      encode_bytes 12 (isin_code record) ++
      encode_uint 1 (series_status record) ++
      encode_uint 1 (effective_tomorrow record) ++
      encode_uint 4 (price_quotation_factor record) ++
      encode_uint 1 (price_method record) ++
      encode_uint 1 (filler_1 record) ++
      encode_bytes 8 (effective_exp_date record) ++
      encode_uint 8 (date_time_last_trading record) ++
      encode_uint 8 (date_time_first_trading record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_bytes 32 bytes with
          | None => None
          | Some (symbol_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (country_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (market_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (instrument_group_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (modifier_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (commodity_code_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (expiry_date_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (strike_price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (contract_size_extended_value, bytes) =>
                                              match decode_bytes 12 bytes with
                                              | None => None
                                              | Some (isin_code_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (series_status_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (effective_tomorrow_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (price_quotation_factor_value, bytes) =>
                                                              match decode_uint 1 bytes with
                                                              | None => None
                                                              | Some (price_method_value, bytes) =>
                                                                  match decode_uint 1 bytes with
                                                                  | None => None
                                                                  | Some (filler_1_value, bytes) =>
                                                                      match decode_bytes 8 bytes with
                                                                      | None => None
                                                                      | Some (effective_exp_date_value, bytes) =>
                                                                          match decode_uint 8 bytes with
                                                                          | None => None
                                                                          | Some (date_time_last_trading_value, bytes) =>
                                                                              match decode_uint 8 bytes with
                                                                              | None => None
                                                                              | Some (date_time_first_trading_value, bytes) =>
                                                                                  Some ({| orderbook_id := orderbook_id_value; symbol := symbol_value; country := country_value; market := market_value; instrument_group := instrument_group_value; modifier := modifier_value; commodity_code := commodity_code_value; expiry_date := expiry_date_value; strike_price := strike_price_value; contract_size_extended := contract_size_extended_value; isin_code := isin_code_value; series_status := series_status_value; effective_tomorrow := effective_tomorrow_value; price_quotation_factor := price_quotation_factor_value; price_method := price_method_value; filler_1 := filler_1_value; effective_exp_date := effective_exp_date_value; date_time_last_trading := date_time_last_trading_value; date_time_first_trading := date_time_first_trading_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 100.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 [bound_17 bound_18]]]]]]]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_bytes by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      rewrite decode_encode_uint by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SeriesDefinitionExtendedMessage.

  Module CombinationDefinitionMessage.

    (** Describes a combination orderbook *)
    Record t := {
      combo_orderbook_id : N;
      leg_orderbook_id : N;
      filler_3 : N;
      leg_side : list byte;
      leg_ratio : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (combo_orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (leg_orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N /\
      Datatypes.length (leg_side record) = 1 /\
      (leg_ratio record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (combo_orderbook_id record) ++
      encode_uint 4 (leg_orderbook_id record) ++
      encode_uint 3 (filler_3 record) ++
      encode_bytes 1 (leg_side record) ++
      encode_uint 4 (leg_ratio record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (combo_orderbook_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (leg_orderbook_id_value, bytes) =>
              match decode_uint 3 bytes with
              | None => None
              | Some (filler_3_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (leg_side_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (leg_ratio_value, bytes) =>
                          Some ({| combo_orderbook_id := combo_orderbook_id_value; leg_orderbook_id := leg_orderbook_id_value; filler_3 := filler_3_value; leg_side := leg_side_value; leg_ratio := leg_ratio_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End CombinationDefinitionMessage.

  Module RefreshComplete.

    (** This message is published to mark the end of a refresh cycle *)
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

  End RefreshComplete.

  Module Logon.

    (** Logon *)
    Record t := {
      username : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (username record) = 12.

    Definition encode (record : t) : list byte :=
      encode_bytes 12 (username record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 12 bytes with
      | None => None
      | Some (username_value, bytes) =>
          Some ({| username := username_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
    Proof.
      intros record. unfold encode.
      rewrite !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      unfold decode, encode.
      rewrite decode_encode_bytes by exact bound.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End Logon.

  Module LogonResponse.

    (** LogonResponse *)
    Record t := {
      session_status : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (session_status record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (session_status record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (session_status_value, bytes) =>
          match decode_uint 3 bytes with
          | None => None
          | Some (filler_3_value, bytes) =>
              Some ({| session_status := session_status_value; filler_3 := filler_3_value |}, bytes)
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

  End LogonResponse.

  Module RetransmissionRequest.

    (** RetransmissionRequest *)
    Record t := {
      channel_id : N;
      filler_2 : N;
      begin_seq_num : N;
      end_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_id record) ++
      encode_uint 2 (filler_2 record) ++
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (filler_2_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (begin_seq_num_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (end_seq_num_value, bytes) =>
                      Some ({| channel_id := channel_id_value; filler_2 := filler_2_value; begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End RetransmissionRequest.

  Module RetransmissionResponse.

    (** RetransmissionResponse *)
    Record t := {
      channel_id : N;
      retrans_status : N;
      filler_1 : N;
      begin_seq_num : N;
      end_seq_num : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (channel_id record < 256 ^ N.of_nat 2)%N /\
      (retrans_status record < 256 ^ N.of_nat 1)%N /\
      (filler_1 record < 256 ^ N.of_nat 1)%N /\
      (begin_seq_num record < 256 ^ N.of_nat 4)%N /\
      (end_seq_num record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (channel_id record) ++
      encode_uint 1 (retrans_status record) ++
      encode_uint 1 (filler_1 record) ++
      encode_uint 4 (begin_seq_num record) ++
      encode_uint 4 (end_seq_num record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (channel_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (retrans_status_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (filler_1_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (begin_seq_num_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (end_seq_num_value, bytes) =>
                          Some ({| channel_id := channel_id_value; retrans_status := retrans_status_value; filler_1 := filler_1_value; begin_seq_num := begin_seq_num_value; end_seq_num := end_seq_num_value |}, bytes)
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 12.
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

  End RetransmissionResponse.

  Module SeriesStatisticsMessage.

    (** Provides series information including high, low and open prices *)
    Record t := {
      orderbook_id : N;
      session : N;
      filler_3 : N;
      open : N;
      high : N;
      low : N;
      trade_report_volume : N;
      deal_count : N;
      price : N;
      turnover : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (session record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N /\
      (open record < 256 ^ N.of_nat 4)%N /\
      (high record < 256 ^ N.of_nat 4)%N /\
      (low record < 256 ^ N.of_nat 4)%N /\
      (trade_report_volume record < 256 ^ N.of_nat 8)%N /\
      (deal_count record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 1 (session record) ++
      encode_uint 3 (filler_3 record) ++
      encode_uint 4 (open record) ++
      encode_uint 4 (high record) ++
      encode_uint 4 (low record) ++
      encode_uint 8 (trade_report_volume record) ++
      encode_uint 4 (deal_count record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (turnover record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (session_value, bytes) =>
              match decode_uint 3 bytes with
              | None => None
              | Some (filler_3_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (open_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (high_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (low_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (trade_report_volume_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (deal_count_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (price_value, bytes) =>
                                          match decode_uint 8 bytes with
                                          | None => None
                                          | Some (turnover_value, bytes) =>
                                              Some ({| orderbook_id := orderbook_id_value; session := session_value; filler_3 := filler_3_value; open := open_value; high := high_value; low := low_value; trade_report_volume := trade_report_volume_value; deal_count := deal_count_value; price := price_value; turnover := turnover_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
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
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End SeriesStatisticsMessage.

  Module MarketStatusMessage.

    (** The Market Status message can be used to derive the active state of a series *)
    Record t := {
      state_level : N;
      market : N;
      instrument : N;
      orderbook_id : N;
      commodity_code : N;
      filler_2 : N;
      actual_start_date : list byte;
      actual_start_time : list byte;
      planned_start_date : list byte;
      planned_start_time : list byte;
      seconds_to_state_change : N;
      state : N;
      priority : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (state_level record < 256 ^ N.of_nat 2)%N /\
      (market record < 256 ^ N.of_nat 1)%N /\
      (instrument record < 256 ^ N.of_nat 1)%N /\
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (commodity_code record < 256 ^ N.of_nat 2)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (actual_start_date record) = 8 /\
      Datatypes.length (actual_start_time record) = 6 /\
      Datatypes.length (planned_start_date record) = 8 /\
      Datatypes.length (planned_start_time record) = 6 /\
      (seconds_to_state_change record < 256 ^ N.of_nat 2)%N /\
      (state record < 256 ^ N.of_nat 2)%N /\
      (priority record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (state_level record) ++
      encode_uint 1 (market record) ++
      encode_uint 1 (instrument record) ++
      encode_uint 4 (orderbook_id record) ++
      encode_uint 2 (commodity_code record) ++
      encode_uint 2 (filler_2 record) ++
      encode_bytes 8 (actual_start_date record) ++
      encode_bytes 6 (actual_start_time record) ++
      encode_bytes 8 (planned_start_date record) ++
      encode_bytes 6 (planned_start_time record) ++
      encode_uint 2 (seconds_to_state_change record) ++
      encode_uint 2 (state record) ++
      encode_uint 1 (priority record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (state_level_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (market_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (instrument_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (orderbook_id_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (commodity_code_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (filler_2_value, bytes) =>
                              match decode_bytes 8 bytes with
                              | None => None
                              | Some (actual_start_date_value, bytes) =>
                                  match decode_bytes 6 bytes with
                                  | None => None
                                  | Some (actual_start_time_value, bytes) =>
                                      match decode_bytes 8 bytes with
                                      | None => None
                                      | Some (planned_start_date_value, bytes) =>
                                          match decode_bytes 6 bytes with
                                          | None => None
                                          | Some (planned_start_time_value, bytes) =>
                                              match decode_uint 2 bytes with
                                              | None => None
                                              | Some (seconds_to_state_change_value, bytes) =>
                                                  match decode_uint 2 bytes with
                                                  | None => None
                                                  | Some (state_value, bytes) =>
                                                      match decode_uint 1 bytes with
                                                      | None => None
                                                      | Some (priority_value, bytes) =>
                                                          match decode_uint 3 bytes with
                                                          | None => None
                                                          | Some (filler_3_value, bytes) =>
                                                              Some ({| state_level := state_level_value; market := market_value; instrument := instrument_value; orderbook_id := orderbook_id_value; commodity_code := commodity_code_value; filler_2 := filler_2_value; actual_start_date := actual_start_date_value; actual_start_time := actual_start_time_value; planned_start_date := planned_start_date_value; planned_start_time := planned_start_time_value; seconds_to_state_change := seconds_to_state_change_value; state := state_value; priority := priority_value; filler_3 := filler_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 48.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 bound_13]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End MarketStatusMessage.

  Module SeriesStatusMessage.

    (** The Series Status message is generated whenever there is a change to suspension indicator or series status, or when the date/time of last trading is changed *)
    Record t := {
      orderbook_id : N;
      suspension_indicator : N;
      series_status : N;
      filler_2 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (suspension_indicator record < 256 ^ N.of_nat 1)%N /\
      (series_status record < 256 ^ N.of_nat 1)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 1 (suspension_indicator record) ++
      encode_uint 1 (series_status record) ++
      encode_uint 2 (filler_2 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 1 bytes with
          | None => None
          | Some (suspension_indicator_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (series_status_value, bytes) =>
                  match decode_uint 2 bytes with
                  | None => None
                  | Some (filler_2_value, bytes) =>
                      Some ({| orderbook_id := orderbook_id_value; suspension_indicator := suspension_indicator_value; series_status := series_status_value; filler_2 := filler_2_value |}, bytes)
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

  End SeriesStatusMessage.

  Module CommodityStatusMessage.

    (** The Commodity Status message is generated whenever a commodity status changes *)
    Record t := {
      commodity_code : N;
      suspended : list byte;
      locked : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (commodity_code record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (suspended record) = 1 /\
      (locked record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (commodity_code record) ++
      encode_bytes 1 (suspended record) ++
      encode_uint 1 (locked record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (commodity_code_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (suspended_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (locked_value, bytes) =>
                  Some ({| commodity_code := commodity_code_value; suspended := suspended_value; locked := locked_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 4.
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

  End CommodityStatusMessage.

  Module TradeAmendmentMessage.

    (** Represents a trade amendment or cancellation *)
    Record t := {
      trade_id : N;
      combo_group_id : N;
      price : N;
      quantity : N;
      trade_time : N;
      trade_state : N;
      filler_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (trade_id record < 256 ^ N.of_nat 8)%N /\
      (combo_group_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (trade_time record < 256 ^ N.of_nat 8)%N /\
      (trade_state record < 256 ^ N.of_nat 1)%N /\
      (filler_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (trade_id record) ++
      encode_uint 4 (combo_group_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 8 (trade_time record) ++
      encode_uint 1 (trade_state record) ++
      encode_uint 3 (filler_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (trade_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (combo_group_id_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (price_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_time_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (trade_state_value, bytes) =>
                              match decode_uint 3 bytes with
                              | None => None
                              | Some (filler_3_value, bytes) =>
                                  Some ({| trade_id := trade_id_value; combo_group_id := combo_group_id_value; price := price_value; quantity := quantity_value; trade_time := trade_time_value; trade_state := trade_state_value; filler_3 := filler_3_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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

  End TradeAmendmentMessage.

  Module TradeStatisticsMessage.

    (** Trade information for completed deals *)
    Record t := {
      orderbook_id : N;
      price : N;
      deal_source : N;
      session : N;
      filler_2 : N;
      statistics_aggregate_quantity : N;
      open : N;
      high : N;
      low : N;
      filler_4 : N;
      trade_report_volume : N;
      deal_count : N;
      turnover : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (orderbook_id record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (deal_source record < 256 ^ N.of_nat 1)%N /\
      (session record < 256 ^ N.of_nat 1)%N /\
      (filler_2 record < 256 ^ N.of_nat 2)%N /\
      (statistics_aggregate_quantity record < 256 ^ N.of_nat 8)%N /\
      (open record < 256 ^ N.of_nat 4)%N /\
      (high record < 256 ^ N.of_nat 4)%N /\
      (low record < 256 ^ N.of_nat 4)%N /\
      (filler_4 record < 256 ^ N.of_nat 4)%N /\
      (trade_report_volume record < 256 ^ N.of_nat 8)%N /\
      (deal_count record < 256 ^ N.of_nat 4)%N /\
      (turnover record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (orderbook_id record) ++
      encode_uint 4 (price record) ++
      encode_uint 1 (deal_source record) ++
      encode_uint 1 (session record) ++
      encode_uint 2 (filler_2 record) ++
      encode_uint 8 (statistics_aggregate_quantity record) ++
      encode_uint 4 (open record) ++
      encode_uint 4 (high record) ++
      encode_uint 4 (low record) ++
      encode_uint 4 (filler_4 record) ++
      encode_uint 8 (trade_report_volume record) ++
      encode_uint 4 (deal_count record) ++
      encode_uint 8 (turnover record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (orderbook_id_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (price_value, bytes) =>
              match decode_uint 1 bytes with
              | None => None
              | Some (deal_source_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (session_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (filler_2_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (statistics_aggregate_quantity_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (open_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (high_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (low_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (filler_4_value, bytes) =>
                                              match decode_uint 8 bytes with
                                              | None => None
                                              | Some (trade_report_volume_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (deal_count_value, bytes) =>
                                                      match decode_uint 8 bytes with
                                                      | None => None
                                                      | Some (turnover_value, bytes) =>
                                                          Some ({| orderbook_id := orderbook_id_value; price := price_value; deal_source := deal_source_value; session := session_value; filler_2 := filler_2_value; statistics_aggregate_quantity := statistics_aggregate_quantity_value; open := open_value; high := high_value; low := low_value; filler_4 := filler_4_value; trade_report_volume := trade_report_volume_value; deal_count := deal_count_value; turnover := turnover_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 56.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
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
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End TradeStatisticsMessage.

End HkexDerivativesCombinedRetransV149.
