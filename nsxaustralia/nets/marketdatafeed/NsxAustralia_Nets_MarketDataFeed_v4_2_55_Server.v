From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * Nation Stock Exchange of Australia NSX Market Data Feed

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
  *)

Module NsxAustraliaNetsMarketDataFeedV4255Server.

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

  Module TimestampMessage.

    (** This message is sent to provide the time since Epoch. It should be used in combination with the Timestamp field of individual messages to determine the exact time for each message. *)
    Record t := {
      nanosecond : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (nanosecond record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 8 (nanosecond record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 8 bytes with
      | None => None
      | Some (nanosecond_value, bytes) =>
          Some ({| nanosecond := nanosecond_value |}, bytes)
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 8.
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

  End TimestampMessage.

  Module SystemEventMessage.

    (** This message will be sent to provide information about events that are scheduled or triggered by the system. Events may occur at Orderbook, Board, Board+Product or System level. *)
    Record t := {
      timestamp : N;
      group : list byte;
      product : list byte;
      orderbook : N;
      event_code : list byte;
      event_status : list byte;
      scheduled_time : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (group record) = 20 /\
      Datatypes.length (product record) = 12 /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (event_code record) = 12 /\
      Datatypes.length (event_status record) = 1 /\
      (scheduled_time record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_bytes 20 (group record) ++
      encode_bytes 12 (product record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 12 (event_code record) ++
      encode_bytes 1 (event_status record) ++
      encode_uint 8 (scheduled_time record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_bytes 20 bytes with
          | None => None
          | Some (group_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (product_value, bytes) =>
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (orderbook_value, bytes) =>
                      match decode_bytes 12 bytes with
                      | None => None
                      | Some (event_code_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (event_status_value, bytes) =>
                              match decode_uint 8 bytes with
                              | None => None
                              | Some (scheduled_time_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; group := group_value; product := product_value; orderbook := orderbook_value; event_code := event_code_value; event_status := event_status_value; scheduled_time := scheduled_time_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 61.
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
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SystemEventMessage.

  Module PriceTickSizeMessage.

    (** This message provides the price ticks (steps) for the orderbooks in the system. It should be used as a lookup from Orderbook Directory [R] messages. *)
    Record t := {
      timestamp : N;
      tick_size_table_id : N;
      tick_size : N;
      price_start : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N /\
      (price_start record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (tick_size_table_id record) ++
      encode_uint 8 (tick_size record) ++
      encode_uint 8 (price_start record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (tick_size_table_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tick_size_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (price_start_value, bytes) =>
                      Some ({| timestamp := timestamp_value; tick_size_table_id := tick_size_table_id_value; tick_size := tick_size_value; price_start := price_start_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End PriceTickSizeMessage.

  Module QuantityTickSizeMessage.

    (** This message provides the quantity ticks (steps) for the orderbooks in the system. It should be used as a lookup from Orderbook Directory [R] messages. *)
    Record t := {
      timestamp : N;
      tick_size_table_id : N;
      tick_size : N;
      quantity_start : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (tick_size record < 256 ^ N.of_nat 8)%N /\
      (quantity_start record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (tick_size_table_id record) ++
      encode_uint 8 (tick_size record) ++
      encode_uint 8 (quantity_start record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (tick_size_table_id_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (tick_size_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_start_value, bytes) =>
                      Some ({| timestamp := timestamp_value; tick_size_table_id := tick_size_table_id_value; tick_size := tick_size_value; quantity_start := quantity_start_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 24.
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

  End QuantityTickSizeMessage.

  Module OrderbookDirectoryMessage.

    (** Orderbook Directory Messages are transmitted during the reference data spin. Static data messages are sent at the beginning of the feed and contain exchange reference information. *)
    Record t := {
      timestamp : N;
      orderbook : N;
      isin : list byte;
      security_code : list byte;
      security_name : list byte;
      currency : list byte;
      board : list byte;
      product : list byte;
      minimum_quantity : N;
      quantity_tick_size_table_id : N;
      quantity_decimals : N;
      price_tick_size_table_id : N;
      price_decimals : N;
      listing : N;
      expiry : N;
      asset_type : list byte;
      settle_date : N;
      reference_alpha_12 : list byte;
      remarks : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (isin record) = 12 /\
      Datatypes.length (security_code record) = 100 /\
      Datatypes.length (security_name record) = 100 /\
      Datatypes.length (currency record) = 3 /\
      Datatypes.length (board record) = 20 /\
      Datatypes.length (product record) = 12 /\
      (minimum_quantity record < 256 ^ N.of_nat 8)%N /\
      (quantity_tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (quantity_decimals record < 256 ^ N.of_nat 4)%N /\
      (price_tick_size_table_id record < 256 ^ N.of_nat 4)%N /\
      (price_decimals record < 256 ^ N.of_nat 4)%N /\
      (listing record < 256 ^ N.of_nat 8)%N /\
      (expiry record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (asset_type record) = 1 /\
      (settle_date record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (reference_alpha_12 record) = 12 /\
      Datatypes.length (remarks record) = 8.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 12 (isin record) ++
      encode_bytes 100 (security_code record) ++
      encode_bytes 100 (security_name record) ++
      encode_bytes 3 (currency record) ++
      encode_bytes 20 (board record) ++
      encode_bytes 12 (product record) ++
      encode_uint 8 (minimum_quantity record) ++
      encode_uint 4 (quantity_tick_size_table_id record) ++
      encode_uint 4 (quantity_decimals record) ++
      encode_uint 4 (price_tick_size_table_id record) ++
      encode_uint 4 (price_decimals record) ++
      encode_uint 8 (listing record) ++
      encode_uint 8 (expiry record) ++
      encode_bytes 1 (asset_type record) ++
      encode_uint 4 (settle_date record) ++
      encode_bytes 12 (reference_alpha_12 record) ++
      encode_bytes 8 (remarks record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_bytes 12 bytes with
              | None => None
              | Some (isin_value, bytes) =>
                  match decode_bytes 100 bytes with
                  | None => None
                  | Some (security_code_value, bytes) =>
                      match decode_bytes 100 bytes with
                      | None => None
                      | Some (security_name_value, bytes) =>
                          match decode_bytes 3 bytes with
                          | None => None
                          | Some (currency_value, bytes) =>
                              match decode_bytes 20 bytes with
                              | None => None
                              | Some (board_value, bytes) =>
                                  match decode_bytes 12 bytes with
                                  | None => None
                                  | Some (product_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (minimum_quantity_value, bytes) =>
                                          match decode_uint 4 bytes with
                                          | None => None
                                          | Some (quantity_tick_size_table_id_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (quantity_decimals_value, bytes) =>
                                                  match decode_uint 4 bytes with
                                                  | None => None
                                                  | Some (price_tick_size_table_id_value, bytes) =>
                                                      match decode_uint 4 bytes with
                                                      | None => None
                                                      | Some (price_decimals_value, bytes) =>
                                                          match decode_uint 8 bytes with
                                                          | None => None
                                                          | Some (listing_value, bytes) =>
                                                              match decode_uint 8 bytes with
                                                              | None => None
                                                              | Some (expiry_value, bytes) =>
                                                                  match decode_bytes 1 bytes with
                                                                  | None => None
                                                                  | Some (asset_type_value, bytes) =>
                                                                      match decode_uint 4 bytes with
                                                                      | None => None
                                                                      | Some (settle_date_value, bytes) =>
                                                                          match decode_bytes 12 bytes with
                                                                          | None => None
                                                                          | Some (reference_alpha_12_value, bytes) =>
                                                                              match decode_bytes 8 bytes with
                                                                              | None => None
                                                                              | Some (remarks_value, bytes) =>
                                                                                  Some ({| timestamp := timestamp_value; orderbook := orderbook_value; isin := isin_value; security_code := security_code_value; security_name := security_name_value; currency := currency_value; board := board_value; product := product_value; minimum_quantity := minimum_quantity_value; quantity_tick_size_table_id := quantity_tick_size_table_id_value; quantity_decimals := quantity_decimals_value; price_tick_size_table_id := price_tick_size_table_id_value; price_decimals := price_decimals_value; listing := listing_value; expiry := expiry_value; asset_type := asset_type_value; settle_date := settle_date_value; reference_alpha_12 := reference_alpha_12_value; remarks := remarks_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 320.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_uint by exact bound_12.
      rewrite decode_encode_uint by exact bound_13.
      rewrite decode_encode_uint by exact bound_14.
      rewrite decode_encode_bytes by exact bound_15.
      rewrite decode_encode_uint by exact bound_16.
      rewrite decode_encode_bytes by exact bound_17.
      rewrite decode_encode_bytes by exact bound_18.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookDirectoryMessage.

  Module OrderbookTradingActionMessage.

    (** This message indicates the current trading state of an orderbook. *)
    Record t := {
      timestamp : N;
      orderbook : N;
      trading_state : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trading_state record) = 1 /\
      Datatypes.length (reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (trading_state record) ++
      encode_bytes 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (trading_state_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (reason_value, bytes) =>
                      Some ({| timestamp := timestamp_value; orderbook := orderbook_value; trading_state := trading_state_value; reason := reason_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 10.
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
      rewrite decode_encode_bytes by exact bound_3.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookTradingActionMessage.

  Module OrderbookAttributeMessage.

    (** This message provides dynamic reference values for an orderbook. *)
    Record t := {
      timestamp : N;
      orderbook : N;
      attribute_value : N;
      attribute_type : list byte;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (attribute_value record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (attribute_type record) = 1 /\
      Datatypes.length (reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 8 (attribute_value record) ++
      encode_bytes 1 (attribute_type record) ++
      encode_bytes 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (attribute_value_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (attribute_type_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (reason_value, bytes) =>
                          Some ({| timestamp := timestamp_value; orderbook := orderbook_value; attribute_value := attribute_value_value; attribute_type := attribute_type_value; reason := reason_value |}, bytes)
                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 bound_4]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderbookAttributeMessage.

  Module FirmDirectoryMessage.

    (** This message provides reference information about system participants. *)
    Record t := {
      timestamp : N;
      firm_id : N;
      firm_code : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (firm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_code record) = 30.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (firm_id record) ++
      encode_bytes 30 (firm_code record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (firm_id_value, bytes) =>
              match decode_bytes 30 bytes with
              | None => None
              | Some (firm_code_value, bytes) =>
                  Some ({| timestamp := timestamp_value; firm_id := firm_id_value; firm_code := firm_code_value |}, bytes)
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

  End FirmDirectoryMessage.

  Module AddOrderMessage.

    (** This message is sent when an order is added to the orderbook. *)
    Record t := {
      timestamp : N;
      order_number : N;
      order_verb : list byte;
      quantity : N;
      orderbook : N;
      price : N;
      firm_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (order_verb record) = 1 /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (price record < 256 ^ N.of_nat 8)%N /\
      (firm_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_bytes 1 (order_verb record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 8 (price record) ++
      encode_uint 4 (firm_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (order_verb_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (orderbook_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (price_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (firm_id_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; order_number := order_number_value; order_verb := order_verb_value; quantity := quantity_value; orderbook := orderbook_value; price := price_value; firm_id := firm_id_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_bytes by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderMessage.

  Module OrderExecutedMessage.

    (** This message is sent when an order on the book is executed in whole or in part. *)
    Record t := {
      timestamp : N;
      order_number : N;
      executed_quantity : N;
      match_number : N;
      printable : list byte;
      aggressor_firm_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (printable record) = 1 /\
      (aggressor_firm_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 4 (aggressor_firm_id record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (printable_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (aggressor_firm_id_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; printable := printable_value; aggressor_firm_id := aggressor_firm_id_value |}, bytes)
                          end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 bound_5]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedMessage.

  Module OrderExecutedWithPriceMessage.

    (** This message is sent when an order on the book is executed in whole or in part at a negotiated price different from the order price. *)
    Record t := {
      timestamp : N;
      order_number : N;
      executed_quantity : N;
      match_number : N;
      printable : list byte;
      execution_price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (printable record) = 1 /\
      (execution_price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 8 (execution_price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (executed_quantity_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (match_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (printable_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (execution_price_value, bytes) =>
                              Some ({| timestamp := timestamp_value; order_number := order_number_value; executed_quantity := executed_quantity_value; match_number := match_number_value; printable := printable_value; execution_price := execution_price_value |}, bytes)
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 37.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End OrderExecutedWithPriceMessage.

  Module BrokenTradeMessage.

    (** This message is sent when a trade is cancelled. *)
    Record t := {
      timestamp : N;
      match_number : N;
      reason : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (reason record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (reason record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (match_number_value, bytes) =>
              match decode_bytes 1 bytes with
              | None => None
              | Some (reason_value, bytes) =>
                  Some ({| timestamp := timestamp_value; match_number := match_number_value; reason := reason_value |}, bytes)
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

  End BrokenTradeMessage.

  Module OrderDeleteMessage.

    (** This message indicates when an order has been removed from the orderbook. *)
    Record t := {
      timestamp : N;
      order_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (order_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (order_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (order_number_value, bytes) =>
              Some ({| timestamp := timestamp_value; order_number := order_number_value |}, bytes)
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
      destruct bound as [bound_0 bound_1].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec]. Defined.

  End OrderDeleteMessage.

  Module OrderReplaceMessage.

    (** This message indicates when an order in the orderbook has been modified. *)
    Record t := {
      timestamp : N;
      original_order_number : N;
      new_order_number : N;
      quantity : N;
      price : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (original_order_number record < 256 ^ N.of_nat 8)%N /\
      (new_order_number record < 256 ^ N.of_nat 8)%N /\
      (quantity record < 256 ^ N.of_nat 8)%N /\
      (price record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (original_order_number record) ++
      encode_uint 8 (new_order_number record) ++
      encode_uint 8 (quantity record) ++
      encode_uint 8 (price record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (original_order_number_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (new_order_number_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (quantity_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (price_value, bytes) =>
                          Some ({| timestamp := timestamp_value; original_order_number := original_order_number_value; new_order_number := new_order_number_value; quantity := quantity_value; price := price_value |}, bytes)
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

  End OrderReplaceMessage.

  Module IndicativePriceQuantityMessage.

    (** This message provides auction information including the theoretical opening price and quantity. *)
    Record t := {
      timestamp : N;
      theoretical_opening_quantity : N;
      orderbook : N;
      best_bid : N;
      best_offer : N;
      theoretical_opening_price : N;
      cross_type : list byte;
      best_bid_size : N;
      best_offer_size : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (theoretical_opening_quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (best_bid record < 256 ^ N.of_nat 8)%N /\
      (best_offer record < 256 ^ N.of_nat 8)%N /\
      (theoretical_opening_price record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (cross_type record) = 1 /\
      (best_bid_size record < 256 ^ N.of_nat 8)%N /\
      (best_offer_size record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (theoretical_opening_quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 8 (best_bid record) ++
      encode_uint 8 (best_offer record) ++
      encode_uint 8 (theoretical_opening_price record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 8 (best_bid_size record) ++
      encode_uint 8 (best_offer_size record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (theoretical_opening_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (best_bid_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (best_offer_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (theoretical_opening_price_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cross_type_value, bytes) =>
                                  match decode_uint 8 bytes with
                                  | None => None
                                  | Some (best_bid_size_value, bytes) =>
                                      match decode_uint 8 bytes with
                                      | None => None
                                      | Some (best_offer_size_value, bytes) =>
                                          Some ({| timestamp := timestamp_value; theoretical_opening_quantity := theoretical_opening_quantity_value; orderbook := orderbook_value; best_bid := best_bid_value; best_offer := best_offer_value; theoretical_opening_price := theoretical_opening_price_value; cross_type := cross_type_value; best_bid_size := best_bid_size_value; best_offer_size := best_offer_size_value |}, bytes)
                                      end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End IndicativePriceQuantityMessage.

  Module TradeMessage.

    (** This message is sent to provide information about off-book matching. *)
    Record t := {
      timestamp : N;
      executed_quantity : N;
      orderbook : N;
      printable : list byte;
      execution_price : N;
      match_number : N;
      trade_indicator : list byte;
      buy_firm_id : N;
      sell_firm_id : N;
      trade_source : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (executed_quantity record < 256 ^ N.of_nat 8)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (printable record) = 1 /\
      (execution_price record < 256 ^ N.of_nat 8)%N /\
      (match_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (trade_indicator record) = 1 /\
      (buy_firm_id record < 256 ^ N.of_nat 4)%N /\
      (sell_firm_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_source record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 8 (executed_quantity record) ++
      encode_uint 4 (orderbook record) ++
      encode_bytes 1 (printable record) ++
      encode_uint 8 (execution_price record) ++
      encode_uint 8 (match_number record) ++
      encode_bytes 1 (trade_indicator record) ++
      encode_uint 4 (buy_firm_id record) ++
      encode_uint 4 (sell_firm_id record) ++
      encode_bytes 1 (trade_source record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (executed_quantity_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (orderbook_value, bytes) =>
                  match decode_bytes 1 bytes with
                  | None => None
                  | Some (printable_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (execution_price_value, bytes) =>
                          match decode_uint 8 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (trade_indicator_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (buy_firm_id_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (sell_firm_id_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_source_value, bytes) =>
                                              Some ({| timestamp := timestamp_value; executed_quantity := executed_quantity_value; orderbook := orderbook_value; printable := printable_value; execution_price := execution_price_value; match_number := match_number_value; trade_indicator := trade_indicator_value; buy_firm_id := buy_firm_id_value; sell_firm_id := sell_firm_id_value; trade_source := trade_source_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 [bound_8 bound_9]]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End TradeMessage.

  Module NewsMessage.

    (** This message disseminates exchange news. *)
    Record t := {
      timestamp : N;
      orderbook : N;
      news_id : N;
      firm_code : list byte;
      title : list byte;
      reference_null_terminated_char_256 : list byte;
      news_text : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (orderbook record < 256 ^ N.of_nat 4)%N /\
      (news_id record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (firm_code record) = 30 /\
      Datatypes.length (title record) = 81 /\
      Datatypes.length (reference_null_terminated_char_256 record) = 256 /\
      Datatypes.length (news_text record) = 512.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (orderbook record) ++
      encode_uint 4 (news_id record) ++
      encode_bytes 30 (firm_code record) ++
      encode_bytes 81 (title record) ++
      encode_bytes 256 (reference_null_terminated_char_256 record) ++
      encode_bytes 512 (news_text record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (orderbook_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (news_id_value, bytes) =>
                  match decode_bytes 30 bytes with
                  | None => None
                  | Some (firm_code_value, bytes) =>
                      match decode_bytes 81 bytes with
                      | None => None
                      | Some (title_value, bytes) =>
                          match decode_bytes 256 bytes with
                          | None => None
                          | Some (reference_null_terminated_char_256_value, bytes) =>
                              match decode_bytes 512 bytes with
                              | None => None
                              | Some (news_text_value, bytes) =>
                                  Some ({| timestamp := timestamp_value; orderbook := orderbook_value; news_id := news_id_value; firm_code := firm_code_value; title := title_value; reference_null_terminated_char_256 := reference_null_terminated_char_256_value; news_text := news_text_value |}, bytes)
                              end
                          end
                      end
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 891.
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
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_bytes by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_bytes by exact bound_6.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End NewsMessage.

  Module IndexMemberDirectoryMessage.

    (** This message provides details about index members and their respective weightings within an index. *)
    Record t := {
      timestamp : N;
      index_orderbook : N;
      member_orderbook : N;
      weight : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (index_orderbook record < 256 ^ N.of_nat 4)%N /\
      (member_orderbook record < 256 ^ N.of_nat 4)%N /\
      (weight record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (index_orderbook record) ++
      encode_uint 4 (member_orderbook record) ++
      encode_uint 8 (weight record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (index_orderbook_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (member_orderbook_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (weight_value, bytes) =>
                      Some ({| timestamp := timestamp_value; index_orderbook := index_orderbook_value; member_orderbook := member_orderbook_value; weight := weight_value |}, bytes)
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

  End IndexMemberDirectoryMessage.

  Module IndexValueMessage.

    (** This message disseminates index values to market participants. *)
    Record t := {
      timestamp : N;
      index_orderbook : N;
      index_value : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (timestamp record < 256 ^ N.of_nat 4)%N /\
      (index_orderbook record < 256 ^ N.of_nat 4)%N /\
      (index_value record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 4 (timestamp record) ++
      encode_uint 4 (index_orderbook record) ++
      encode_uint 8 (index_value record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 4 bytes with
      | None => None
      | Some (timestamp_value, bytes) =>
          match decode_uint 4 bytes with
          | None => None
          | Some (index_orderbook_value, bytes) =>
              match decode_uint 8 bytes with
              | None => None
              | Some (index_value_value, bytes) =>
                  Some ({| timestamp := timestamp_value; index_orderbook := index_orderbook_value; index_value := index_value_value |}, bytes)
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

  End IndexValueMessage.

End NsxAustraliaNetsMarketDataFeedV4255Server.
