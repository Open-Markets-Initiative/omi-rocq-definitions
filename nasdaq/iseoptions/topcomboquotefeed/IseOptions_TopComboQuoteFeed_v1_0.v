From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) Ise Top Combo Quote Feed

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
      - a run counted by a field
  *)

Module IseOptionsTopComboQuoteFeedV10.

  Module PacketHeader.

    (** Itch Mold Udp 64 Packet Header *)
    Record t := {
      session : list byte;
      sequence_number : N;
      message_count : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      Datatypes.length (session record) = 10 /\
      (sequence_number record < 256 ^ N.of_nat 8)%N /\
      (message_count record < 256 ^ N.of_nat 2)%N.

    Definition encode (record : t) : list byte :=
      encode_bytes 10 (session record) ++
      encode_uint 8 (sequence_number record) ++
      encode_uint 2 (message_count record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_bytes 10 bytes with
      | None => None
      | Some (session_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (sequence_number_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (message_count_value, bytes) =>
                  Some ({| session := session_value; sequence_number := sequence_number_value; message_count := message_count_value |}, bytes)
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 20.
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

  End PacketHeader.

  Module MessageHeader.

    (** Mold Udp 64 Message Header *)
    Record t := {
      message_length : N;
      message_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (message_length record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (message_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (message_length record) ++
      encode_bytes 1 (message_type record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (message_length_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (message_type_value, bytes) =>
              Some ({| message_length := message_length_value; message_type := message_type_value |}, bytes)
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

  End MessageHeader.

  Module SystemEventMessage.

    (** The system event message type is used to signal a market or data feed handler event. *)
    Record t := {
      timestamp : N;
      event_code : list byte;
      current_year : N;
      current_month : N;
      current_day : N;
      version : N;
      sub_version : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      Datatypes.length (event_code record) = 1 /\
      (current_year record < 256 ^ N.of_nat 2)%N /\
      (current_month record < 256 ^ N.of_nat 1)%N /\
      (current_day record < 256 ^ N.of_nat 1)%N /\
      (version record < 256 ^ N.of_nat 1)%N /\
      (sub_version record < 256 ^ N.of_nat 1)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_bytes 1 (event_code record) ++
      encode_uint 2 (current_year record) ++
      encode_uint 1 (current_month record) ++
      encode_uint 1 (current_day record) ++
      encode_uint 1 (version record) ++
      encode_uint 1 (sub_version record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 1 bytes with
          | None => None
          | Some (event_code_value, bytes) =>
              match decode_uint 2 bytes with
              | None => None
              | Some (current_year_value, bytes) =>
                  match decode_uint 1 bytes with
                  | None => None
                  | Some (current_month_value, bytes) =>
                      match decode_uint 1 bytes with
                      | None => None
                      | Some (current_day_value, bytes) =>
                          match decode_uint 1 bytes with
                          | None => None
                          | Some (version_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (sub_version_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; event_code := event_code_value; current_year := current_year_value; current_month := current_month_value; current_day := current_day_value; version := version_value; sub_version := sub_version_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 13.
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

  End SystemEventMessage.

  Module StrategyOpenClosedMessage.

    (** The options system uses this administrative message to indicate when an strategy has completed the opening process and is now available for auto execution or when the option has closed and is no longer available for auto execution. *)
    Record t := {
      timestamp : N;
      strategy_id : N;
      open_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (open_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (open_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (open_state_value, bytes) =>
                  Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; open_state := open_state_value |}, bytes)
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

  End StrategyOpenClosedMessage.

  Module StrategyTradingActionMessage.

    (** ISE uses this administrative message to indicate the current trading status of a strategy within the ISE Options Market. *)
    Record t := {
      timestamp : N;
      strategy_id : N;
      current_trading_state : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (current_trading_state record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (current_trading_state record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (current_trading_state_value, bytes) =>
                  Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; current_trading_state := current_trading_state_value |}, bytes)
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

  End StrategyTradingActionMessage.

  Module StrategyBestBidAndAskUpdate.

    (** The options system uses this administrative message to indicate when an strategy has completed the opening process and is now available for auto execution or when the option has closed and is no longer available for auto execution. *)
    Record t := {
      timestamp : N;
      strategy_id : N;
      quote_condition : list byte;
      bid_price : N;
      bid_size : N;
      bid_cust_size : N;
      bid_pro_cust_size : N;
      bid_ntt_size : N;
      bid_market_size : N;
      bid_ntt_market_size : N;
      ask_price : N;
      ask_size : N;
      ask_cust_size : N;
      ask_pro_cust_size : N;
      ask_ntt_size : N;
      ask_market_size : N;
      ask_ntt_market_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (bid_price record < 256 ^ N.of_nat 4)%N /\
      (bid_size record < 256 ^ N.of_nat 4)%N /\
      (bid_cust_size record < 256 ^ N.of_nat 4)%N /\
      (bid_pro_cust_size record < 256 ^ N.of_nat 4)%N /\
      (bid_ntt_size record < 256 ^ N.of_nat 4)%N /\
      (bid_market_size record < 256 ^ N.of_nat 4)%N /\
      (bid_ntt_market_size record < 256 ^ N.of_nat 4)%N /\
      (ask_price record < 256 ^ N.of_nat 4)%N /\
      (ask_size record < 256 ^ N.of_nat 4)%N /\
      (ask_cust_size record < 256 ^ N.of_nat 4)%N /\
      (ask_pro_cust_size record < 256 ^ N.of_nat 4)%N /\
      (ask_ntt_size record < 256 ^ N.of_nat 4)%N /\
      (ask_market_size record < 256 ^ N.of_nat 4)%N /\
      (ask_ntt_market_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (bid_price record) ++
      encode_uint 4 (bid_size record) ++
      encode_uint 4 (bid_cust_size record) ++
      encode_uint 4 (bid_pro_cust_size record) ++
      encode_uint 4 (bid_ntt_size record) ++
      encode_uint 4 (bid_market_size record) ++
      encode_uint 4 (bid_ntt_market_size record) ++
      encode_uint 4 (ask_price record) ++
      encode_uint 4 (ask_size record) ++
      encode_uint 4 (ask_cust_size record) ++
      encode_uint 4 (ask_pro_cust_size record) ++
      encode_uint 4 (ask_ntt_size record) ++
      encode_uint 4 (ask_market_size record) ++
      encode_uint 4 (ask_ntt_market_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
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
                                  | Some (bid_ntt_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (bid_market_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (bid_ntt_market_size_value, bytes) =>
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
                                                              | Some (ask_ntt_size_value, bytes) =>
                                                                  match decode_uint 4 bytes with
                                                                  | None => None
                                                                  | Some (ask_market_size_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (ask_ntt_market_size_value, bytes) =>
                                                                          Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; quote_condition := quote_condition_value; bid_price := bid_price_value; bid_size := bid_size_value; bid_cust_size := bid_cust_size_value; bid_pro_cust_size := bid_pro_cust_size_value; bid_ntt_size := bid_ntt_size_value; bid_market_size := bid_market_size_value; bid_ntt_market_size := bid_ntt_market_size_value; ask_price := ask_price_value; ask_size := ask_size_value; ask_cust_size := ask_cust_size_value; ask_pro_cust_size := ask_pro_cust_size_value; ask_ntt_size := ask_ntt_size_value; ask_market_size := ask_market_size_value; ask_ntt_market_size := ask_ntt_market_size_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 67.
    Proof.
      intros record. unfold encode.
      rewrite !length_app, !encode_uint_length, !encode_bytes_length. reflexivity.
    Qed.

    Theorem decode_encode :
      forall record after, bounded record -> decode (encode record ++ after) = Some (record, after).
    Proof.
      intros record after bound.
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 [bound_9 [bound_10 [bound_11 [bound_12 [bound_13 [bound_14 [bound_15 bound_16]]]]]]]]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
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
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_uint by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyBestBidAndAskUpdate.

  Module StrategyBestBidUpdate.

    (** The options system will continuously calculate its best bid position for active strategies on the options market during the trading day. Whenever the best bid position changes on one side but not the other side, the options system will send its best bid update via this feed for the affected security. *)
    Record t := {
      timestamp : N;
      strategy_id : N;
      quote_condition : list byte;
      price : N;
      size : N;
      cust_size : N;
      pro_cust_size : N;
      ntt_size : N;
      market_size : N;
      ntt_market_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (cust_size record < 256 ^ N.of_nat 4)%N /\
      (pro_cust_size record < 256 ^ N.of_nat 4)%N /\
      (ntt_size record < 256 ^ N.of_nat 4)%N /\
      (market_size record < 256 ^ N.of_nat 4)%N /\
      (ntt_market_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (size record) ++
      encode_uint 4 (cust_size record) ++
      encode_uint 4 (pro_cust_size record) ++
      encode_uint 4 (ntt_size record) ++
      encode_uint 4 (market_size record) ++
      encode_uint 4 (ntt_market_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
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
                                  | Some (ntt_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (market_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (ntt_market_size_value, bytes) =>
                                              Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; quote_condition := quote_condition_value; price := price_value; size := size_value; cust_size := cust_size_value; pro_cust_size := pro_cust_size_value; ntt_size := ntt_size_value; market_size := market_size_value; ntt_market_size := ntt_market_size_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyBestBidUpdate.

  Module StrategyBestAskUpdate.

    (** The options system will continuously calculate its best offer position for active strategies on the options market during the trading day. Whenever the best ask position changes on one side but not the other side, the options system will send its best ask update via this feed for the affected security *)
    Record t := {
      timestamp : N;
      strategy_id : N;
      quote_condition : list byte;
      price : N;
      size : N;
      cust_size : N;
      pro_cust_size : N;
      ntt_size : N;
      market_size : N;
      ntt_market_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (quote_condition record) = 1 /\
      (price record < 256 ^ N.of_nat 4)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (cust_size record < 256 ^ N.of_nat 4)%N /\
      (pro_cust_size record < 256 ^ N.of_nat 4)%N /\
      (ntt_size record < 256 ^ N.of_nat 4)%N /\
      (market_size record < 256 ^ N.of_nat 4)%N /\
      (ntt_market_size record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_bytes 1 (quote_condition record) ++
      encode_uint 4 (price record) ++
      encode_uint 4 (size record) ++
      encode_uint 4 (cust_size record) ++
      encode_uint 4 (pro_cust_size record) ++
      encode_uint 4 (ntt_size record) ++
      encode_uint 4 (market_size record) ++
      encode_uint 4 (ntt_market_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
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
                                  | Some (ntt_size_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (market_size_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (ntt_market_size_value, bytes) =>
                                              Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; quote_condition := quote_condition_value; price := price_value; size := size_value; cust_size := cust_size_value; pro_cust_size := pro_cust_size_value; ntt_size := ntt_size_value; market_size := market_size_value; ntt_market_size := ntt_market_size_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 39.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
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
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End StrategyBestAskUpdate.

  Module ComplexStrategyTickerMessage.

    (** The ticker message is used to send real time trade information *)
    Record t := {
      timestamp : N;
      strategy_id : N;
      last_price : N;
      size : N;
      volume : N;
      high : N;
      low : N;
      first : N;
      trade_condition : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 6)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (last_price record < 256 ^ N.of_nat 8)%N /\
      (size record < 256 ^ N.of_nat 4)%N /\
      (volume record < 256 ^ N.of_nat 4)%N /\
      (high record < 256 ^ N.of_nat 8)%N /\
      (low record < 256 ^ N.of_nat 8)%N /\
      (first record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_condition record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 6 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (last_price record) ++
      encode_uint 4 (size record) ++
      encode_uint 4 (volume record) ++
      encode_uint 8 (high record) ++
      encode_uint 8 (low record) ++
      encode_uint 8 (first record) ++
      encode_bytes 1 (trade_condition record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 6 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (strategy_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (last_price_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (size_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (volume_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (high_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (low_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (first_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (trade_condition_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; strategy_id := strategy_id_value; last_price := last_price_value; size := size_value; volume := volume_value; high := high_value; low := low_value; first := first_value; trade_condition := trade_condition_value |}, bytes)
                                      end
                                  end
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 51.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexStrategyTickerMessage.

End IseOptionsTopComboQuoteFeedV10.
