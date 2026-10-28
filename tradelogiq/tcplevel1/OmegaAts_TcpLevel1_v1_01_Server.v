From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Tradelogiq Markets Inc. Omega Tcp Level 1

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
      - a field present only on a condition
  *)

Module OmegaAtsTcpLevel1V101Server.

  Module ServerPacketHeader.

    (** Tradelogiq SoupTcp Server Packet Header *)
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

    (** The server sends a Login Accepted Packet in response to receiving a valid Login Request from the client *)
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

    (** The server sends this packet in response to an invalid Login Request Packet from the client and closes the socket connection *)
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

  Module QuoteMessage.

    (** Tradelogiq's BBO will broadcast real-time updates every time Tradelogiq's top of book changes. *)
    Record t := {
      reserved_1 : N;
      stock_symbol : list byte;
      timestamp : N;
      best_bid_price : N;
      best_bid_size : N;
      best_ask_price : N;
      best_ask_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock_symbol record) = 10 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (best_bid_price record < 256 ^ N.of_nat 8)%N /\
      (best_bid_size record < 256 ^ N.of_nat 4)%N /\
      (best_ask_price record < 256 ^ N.of_nat 8)%N /\
      (best_ask_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 8 (best_bid_price record) ++
      encode_uint 4 (best_bid_size record) ++
      encode_uint 8 (best_ask_price record) ++
      encode_uint 4 (best_ask_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (best_bid_price_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (best_bid_size_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (best_ask_price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (best_ask_size_value, bytes) =>
                                  Some ({| reserved_1 := reserved_1_value; stock_symbol := stock_symbol_value; timestamp := timestamp_value; best_bid_price := best_bid_price_value; best_bid_size := best_bid_size_value; best_ask_price := best_ask_price_value; best_ask_size := best_ask_size_value |}, bytes)
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

  End QuoteMessage.

  Module TradeReportMessage.

    (** Relays all transactions available from or reported by Tradelogiq's two trading books for the current business day. *)
    Record t := {
      conditions : list byte;
      stock_symbol : list byte;
      timestamp : N;
      trade_id : N;
      trade_price : N;
      trade_size : N;
      buy_broker : N;
      sell_broker : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (conditions record) = 5 /\
      Datatypes.length (stock_symbol record) = 10 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N /\
      (trade_price record < 256 ^ N.of_nat 8)%N /\
      (trade_size record < 256 ^ N.of_nat 4)%N /\
      (buy_broker record < 256 ^ N.of_nat 2)%N /\
      (sell_broker record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 5 (conditions record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (trade_id record) ++
      encode_uint 8 (trade_price record) ++
      encode_uint 4 (trade_size record) ++
      encode_uint 2 (buy_broker record) ++
      encode_uint 2 (sell_broker record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 5 bytes with
      | None => None
      | Some (conditions_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (trade_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (trade_size_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (buy_broker_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (sell_broker_value, bytes) =>
                                      Some ({| conditions := conditions_value; stock_symbol := stock_symbol_value; timestamp := timestamp_value; trade_id := trade_id_value; trade_price := trade_price_value; trade_size := trade_size_value; buy_broker := buy_broker_value; sell_broker := sell_broker_value |}, bytes)
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

  End TradeReportMessage.

  Module TradeBustMessage.

    (** If trade is cancelled or busted during the day Trade Bust Message will be sent. *)
    Record t := {
      reserved_1 : N;
      stock_symbol : list byte;
      timestamp : N;
      trade_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock_symbol record) = 10 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (trade_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (trade_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (trade_id_value, bytes) =>
                      Some ({| reserved_1 := reserved_1_value; stock_symbol := stock_symbol_value; timestamp := timestamp_value; trade_id := trade_id_value |}, bytes)
                  end
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

  End TradeBustMessage.

  Module TradeCorrectionMessage.

    (** Trade amendments during the day will send this message. *)
    Record t := {
      reserved_1 : N;
      stock_symbol : list byte;
      timestamp : N;
      original_trade_id : N;
      original_trade_price : N;
      original_trade_size : N;
      corrected_trade_price : N;
      corrected_trade_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (stock_symbol record) = 10 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (original_trade_id record < 256 ^ N.of_nat 4)%N /\
      (original_trade_price record < 256 ^ N.of_nat 8)%N /\
      (original_trade_size record < 256 ^ N.of_nat 4)%N /\
      (corrected_trade_price record < 256 ^ N.of_nat 8)%N /\
      (corrected_trade_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 10 (stock_symbol record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (original_trade_id record) ++
      encode_uint 8 (original_trade_price record) ++
      encode_uint 4 (original_trade_size record) ++
      encode_uint 8 (corrected_trade_price record) ++
      encode_uint 4 (corrected_trade_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 1 bytes with
      | None => None
      | Some (reserved_1_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_symbol_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (original_trade_id_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (original_trade_price_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (original_trade_size_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (corrected_trade_price_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (corrected_trade_size_value, bytes) =>
                                      Some ({| reserved_1 := reserved_1_value; stock_symbol := stock_symbol_value; timestamp := timestamp_value; original_trade_id := original_trade_id_value; original_trade_price := original_trade_price_value; original_trade_size := original_trade_size_value; corrected_trade_price := corrected_trade_price_value; corrected_trade_size := corrected_trade_size_value |}, bytes)
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 47.
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

  End TradeCorrectionMessage.

  Module SystemEventMessage.

    (** The system event message is used to signal a market or a data feed handler event. *)
    Record t := {
      event_code : list byte;
      reserved_2 : N;
      timestamp : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (event_code record) = 1 /\
      (reserved_2 record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (event_code record) ++
      encode_uint 2 (reserved_2 record) ++
      encode_uint 8 (timestamp record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (event_code_value, bytes) =>
          match decode_uint 2 bytes with
          | None => None
          | Some (reserved_2_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  Some ({| event_code := event_code_value; reserved_2 := reserved_2_value; timestamp := timestamp_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 11.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 bound_2]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module StockDirectoryMessage.

    (** At start of each trading day, OSI disseminates stock directory messages for supported securities. *)
    Record t := {
      market : list byte;
      stock : list byte;
      timestamp : N;
      board_lot_size : N;
      instrument_id : N;
      shortable : list byte;
      dividend_indicator : list byte;
      reserved_9 : list byte;
      currency : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market record) = 1 /\
      Datatypes.length (stock record) = 10 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (board_lot_size record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (shortable record) = 1 /\
      Datatypes.length (dividend_indicator record) = 1 /\
      Datatypes.length (reserved_9 record) = 9 /\
      Datatypes.length (currency record) = 3.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market record) ++
      encode_bytes 10 (stock record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (board_lot_size record) ++
      encode_uint 2 (instrument_id record) ++
      encode_bytes 1 (shortable record) ++
      encode_bytes 1 (dividend_indicator record) ++
      encode_bytes 9 (reserved_9 record) ++
      encode_bytes 3 (currency record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (board_lot_size_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (shortable_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (dividend_indicator_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (reserved_9_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (currency_value, bytes) =>
                                          Some ({| market := market_value; stock := stock_value; timestamp := timestamp_value; board_lot_size := board_lot_size_value; instrument_id := instrument_id_value; shortable := shortable_value; dividend_indicator := dividend_indicator_value; reserved_9 := reserved_9_value; currency := currency_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockDirectoryMessage.

  Module ExtendedStockDirectoryMessage.

    (** Extended Stock Directory are for Special stock symbols eg warrants debentures rights. *)
    Record t := {
      market : list byte;
      stock : list byte;
      timestamp : N;
      board_lot_size : N;
      instrument_id : N;
      shortable : list byte;
      frequency : list byte;
      reserved_9 : list byte;
      currency : list byte;
      security_type : list byte;
      expiry_date : list byte;
      description : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (market record) = 1 /\
      Datatypes.length (stock record) = 10 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (board_lot_size record < 256 ^ N.of_nat 4)%N /\
      (instrument_id record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (shortable record) = 1 /\
      Datatypes.length (frequency record) = 1 /\
      Datatypes.length (reserved_9 record) = 9 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (security_type record) = 1 /\
      Datatypes.length (expiry_date record) = 8 /\
      Datatypes.length (description record) = 20 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (market record) ++
      encode_bytes 10 (stock record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (board_lot_size record) ++
      encode_uint 2 (instrument_id record) ++
      encode_bytes 1 (shortable record) ++
      encode_bytes 1 (frequency record) ++
      encode_bytes 9 (reserved_9 record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 1 (security_type record) ++
      encode_bytes 8 (expiry_date record) ++
      encode_bytes 20 (description record) ++
      encode_uint 3 (reserved_3 record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (market_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (board_lot_size_value, bytes) =>
                      match decode_uint 2 bytes with
                      | None => None
                      | Some (instrument_id_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (shortable_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (frequency_value, bytes) =>
                                  match decode_bytes 9 bytes with
                                  | None => None
                                  | Some (reserved_9_value, bytes) =>
                                      match decode_bytes 3 bytes with
                                      | None => None
                                      | Some (currency_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (security_type_value, bytes) =>
                                              match decode_bytes 8 bytes with
                                              | None => None
                                              | Some (expiry_date_value, bytes) =>
                                                  match decode_bytes 20 bytes with
                                                  | None => None
                                                  | Some (description_value, bytes) =>
                                                      match decode_uint 3 bytes with
                                                      | None => None
                                                      | Some (reserved_3_value, bytes) =>
                                                          Some ({| market := market_value; stock := stock_value; timestamp := timestamp_value; board_lot_size := board_lot_size_value; instrument_id := instrument_id_value; shortable := shortable_value; frequency := frequency_value; reserved_9 := reserved_9_value; currency := currency_value; security_type := security_type_value; expiry_date := expiry_date_value; description := description_value; reserved_3 := reserved_3_value |}, bytes)
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
      rewrite !length_app, !encode_bytes_length, !encode_uint_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 bound_12]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_bytes by exact bound_0.
      rewrite decode_encode_bytes by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_bytes by exact bound_10.
      rewrite decode_encode_bytes by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ExtendedStockDirectoryMessage.

  Module StockStatusMessage.

    (** This message indicates the current trading status of a stock. *)
    Record t := {
      trading_state : list byte;
      stock : list byte;
      timestamp : N;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (stock record) = 10 /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reason record) = 4.

    Definition encode (record : t) : list byte :=
      encode_bytes 1 (trading_state record) ++
      encode_bytes 10 (stock record) ++
      encode_uint 8 (timestamp record) ++
      encode_bytes 4 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 1 bytes with
      | None => None
      | Some (trading_state_value, bytes) =>
          match decode_bytes 10 bytes with
          | None => None
          | Some (stock_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (timestamp_value, bytes) =>
                  match decode_bytes 4 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      Some ({| trading_state := trading_state_value; stock := stock_value; timestamp := timestamp_value; reason := reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 23.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StockStatusMessage.

End OmegaAtsTcpLevel1V101Server.
