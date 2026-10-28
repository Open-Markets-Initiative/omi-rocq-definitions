From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) ISE Options Spread Top Of Market

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
      - a length prefix framing what follows
      - a run counted by a field
  *)

Module IseOptionsSpreadTopOfMarketV21Server.

  Module ServerPacketHeader.

    (** Packet header of a packet sent by the server *)
    Record t := {
      packet_length : N;
      server_packet_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (packet_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (server_packet_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (packet_length record) ++
      encode_bytes 1 (server_packet_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (packet_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (server_packet_type_value, bytes) =>
              Some ({| packet_length := packet_length_value; server_packet_type := server_packet_type_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 3.
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

  End ServerPacketHeader.

  Module LoginAcceptedPacket.

    (** The SoupBinTCP server sends a Login Accepted Packet in response to receiving a valid Login Request from the client *)
    Record t := {
      accepted_session : list byte;
      accepted_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (accepted_session record) = 10 /\
      Datatypes.length (accepted_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (accepted_session record) ++
      encode_bytes 20 (accepted_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (accepted_session_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (accepted_sequence_number_value, bytes) =>
              Some ({| accepted_session := accepted_session_value; accepted_sequence_number := accepted_sequence_number_value |}, bytes)
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 30.
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

  End LoginAcceptedPacket.

  Module LoginRejectedPacket.

    (** The SoupBinTCP server sends this packet in response to an invalid Login Request Packet from the client *)
    Record t := {
      reject_reason_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (reject_reason_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (reject_reason_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (reject_reason_code_value, bytes) =>
          Some ({| reject_reason_code := reject_reason_code_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 1.
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

  End LoginRejectedPacket.

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      event_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (event_code record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 1 (event_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (event_code_value, bytes) =>
                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; event_code := event_code_value |}, bytes)
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

  End SystemEventMessage.

  Module StrategyTradingActionMessage.

    (** The options system uses this administrative message to indicate the current trading status of an index or equity option within the options market. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (strategy_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (current_trading_state_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; current_trading_state := current_trading_state_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 15.
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyTradingActionMessage.

  Module StrategyBestBidAndAskUpdateMessage.

    (** The options system will continuously calculate its best bid and ask position for active strategies on the options market during the trading day. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      quote_condition : list byte;
      bid_market_size : N;
      bid_price : N;
      bid_size : N;
      bid_cust_size : N;
      bid_pro_cust_size : N;
      bid_dntt_size : N;
      bid_dntt_market_size : N;
      ask_market_size : N;
      ask_price : N;
      ask_size : N;
      ask_cust_size : N;
      ask_pro_cust_size : N;
      ask_dntt_size : N;
      ask_dntt_market_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (bid_market_size record < 256 ^ N.of_nat 4)%N /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (bid_cust_size record < 256 ^ N.of_nat 4)%N /\
      (bid_pro_cust_size record < 256 ^ N.of_nat 4)%N /\
      (bid_dntt_size record < 256 ^ N.of_nat 4)%N /\
      (bid_dntt_market_size record < 256 ^ N.of_nat 4)%N /\
      (ask_market_size record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (ask_size record < 256 ^ N.of_nat 4)%N /\
      (ask_cust_size record < 256 ^ N.of_nat 4)%N /\
      (ask_pro_cust_size record < 256 ^ N.of_nat 4)%N /\
      (ask_dntt_size record < 256 ^ N.of_nat 4)%N /\
      (ask_dntt_market_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (bid_market_size record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (bid_size record) ++
      encode_uint 4 (bid_cust_size record) ++
      encode_uint 4 (bid_pro_cust_size record) ++
      encode_uint 4 (bid_dntt_size record) ++
      encode_uint 4 (bid_dntt_market_size record) ++
      encode_uint 4 (ask_market_size record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 4 (ask_size record) ++
      encode_uint 4 (ask_cust_size record) ++
      encode_uint 4 (ask_pro_cust_size record) ++
      encode_uint 4 (ask_dntt_size record) ++
      encode_uint 4 (ask_dntt_market_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (strategy_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quote_condition_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (bid_market_size_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (bid_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (bid_size_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (bid_cust_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (bid_pro_cust_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (bid_dntt_size_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (bid_dntt_market_size_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (ask_market_size_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (ask_price_value, bytes) =>
                                                          match decode_uint 4 bytes with
                                                          | None => None
                                                          | Some (ask_size_value, bytes) =>
                                                              match decode_uint 4 bytes with
                                                              | None => None
                                                              | Some (ask_cust_size_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (ask_pro_cust_size_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (ask_dntt_size_value, bytes) =>
                                                                          match decode_uint 4 bytes with
                                                                          | None => None
                                                                          | Some (ask_dntt_market_size_value, bytes) =>
                                                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; quote_condition := quote_condition_value; bid_market_size := bid_market_size_value; bid_price := bid_price_value; bid_size := bid_size_value; bid_cust_size := bid_cust_size_value; bid_pro_cust_size := bid_pro_cust_size_value; bid_dntt_size := bid_dntt_size_value; bid_dntt_market_size := bid_dntt_market_size_value; ask_market_size := ask_market_size_value; ask_price := ask_price_value; ask_size := ask_size_value; ask_cust_size := ask_cust_size_value; ask_pro_cust_size := ask_pro_cust_size_value; ask_dntt_size := ask_dntt_size_value; ask_dntt_market_size := ask_dntt_market_size_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 71.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 [bound_16 bound_17]]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
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
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_uint by exact bound_17.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyBestBidAndAskUpdateMessage.

  Module StrategyBestBidUpdateMessage.

    (** Strategy Best bid OR ask update. Quote update bid side. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      quote_condition : list byte;
      market_size : N;
      price : N;
      size : N;
      cust_size : N;
      pro_cust_size : N;
      dntt_size : N;
      dntt_market_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (market_size record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (cust_size record < 256 ^ N.of_nat 4)%N /\
      (pro_cust_size record < 256 ^ N.of_nat 4)%N /\
      (dntt_size record < 256 ^ N.of_nat 4)%N /\
      (dntt_market_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (market_size record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (size record) ++
      encode_uint 4 (cust_size record) ++
      encode_uint 4 (pro_cust_size record) ++
      encode_uint 4 (dntt_size record) ++
      encode_uint 4 (dntt_market_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (strategy_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quote_condition_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (market_size_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (size_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cust_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (pro_cust_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (dntt_size_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (dntt_market_size_value, bytes) =>
                                                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; quote_condition := quote_condition_value; market_size := market_size_value; price := price_value; size := size_value; cust_size := cust_size_value; pro_cust_size := pro_cust_size_value; dntt_size := dntt_size_value; dntt_market_size := dntt_market_size_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyBestBidUpdateMessage.

  Module StrategyBestAskUpdateMessage.

    (** Strategy Best bid OR ask update. Quote update ask side. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      quote_condition : list byte;
      market_size : N;
      price : N;
      size : N;
      cust_size : N;
      pro_cust_size : N;
      dntt_size : N;
      dntt_market_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (market_size record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (cust_size record < 256 ^ N.of_nat 4)%N /\
      (pro_cust_size record < 256 ^ N.of_nat 4)%N /\
      (dntt_size record < 256 ^ N.of_nat 4)%N /\
      (dntt_market_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (market_size record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (size record) ++
      encode_uint 4 (cust_size record) ++
      encode_uint 4 (pro_cust_size record) ++
      encode_uint 4 (dntt_size record) ++
      encode_uint 4 (dntt_market_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (strategy_id_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (quote_condition_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (market_size_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (size_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cust_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (pro_cust_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (dntt_size_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (dntt_market_size_value, bytes) =>
                                                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; quote_condition := quote_condition_value; market_size := market_size_value; price := price_value; size := size_value; cust_size := cust_size_value; pro_cust_size := pro_cust_size_value; dntt_size := dntt_size_value; dntt_market_size := dntt_market_size_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 43.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyBestAskUpdateMessage.

  Module EndOfReplaySequenceMessage.

    (** The End of replay Sequence message reflects the sequence number at the time replay of existing messages is complete. *)
    Record t := {
      end_of_replay_sequence_number : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (end_of_replay_sequence_number record) = 20.

    Definition encode (record : t) : list byte :=
      encode_bytes 20 (end_of_replay_sequence_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 20 bytes with
      | None => None
      | Some (end_of_replay_sequence_number_value, bytes) =>
          Some ({| end_of_replay_sequence_number := end_of_replay_sequence_number_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End EndOfReplaySequenceMessage.

End IseOptionsSpreadTopOfMarketV21Server.
