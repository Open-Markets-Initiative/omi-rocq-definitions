From Stdlib Require Import List.
From Stdlib Require Import NArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.Byte.
From Omi Require Import Wire.

Import ListNotations.

(** * National Association of Securities Dealers Automated Quotations (Nasdaq) ISE Options Spread Depth

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

Module IseOptionsSpreadDepthOfMarketV21Server.

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

  Module AddOrderShortFormMessage.

    (** A Complex Add Order Message indicates that a new order has been accepted and was added to the displayable book. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      order_reference_number : N;
      depth_side : list byte;
      depth_order_capacity : list byte;
      price_short : N;
      volume_short : N;
      scope : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (depth_side record) = 1 /\
      Datatypes.length (depth_order_capacity record) = 1 /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (volume_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (scope record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (depth_side record) ++
      encode_bytes 1 (depth_order_capacity record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 2 (volume_short record) ++
      encode_bytes 1 (scope record) ++
      encode_uint 3 (reserved_3 record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (depth_side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (depth_order_capacity_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (price_short_value, bytes) =>
                                  match decode_uint 2 bytes with
                                  | None => None
                                  | Some (volume_short_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (scope_value, bytes) =>
                                          match decode_uint 3 bytes with
                                          | None => None
                                          | Some (reserved_3_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; order_reference_number := order_reference_number_value; depth_side := depth_side_value; depth_order_capacity := depth_order_capacity_value; price_short := price_short_value; volume_short := volume_short_value; scope := scope_value; reserved_3 := reserved_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 32.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderShortFormMessage.

  Module AddOrderLongFormMessage.

    (** A Complex Add Order Message indicates that a new order has been accepted and was added to the displayable book. Long form. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      order_reference_number : N;
      depth_side : list byte;
      depth_order_capacity : list byte;
      price_long : N;
      volume_long : N;
      scope : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (depth_side record) = 1 /\
      Datatypes.length (depth_order_capacity record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (scope record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (depth_side record) ++
      encode_bytes 1 (depth_order_capacity record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record) ++
      encode_bytes 1 (scope record) ++
      encode_uint 3 (reserved_3 record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (depth_side_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (depth_order_capacity_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (price_long_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (volume_long_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (scope_value, bytes) =>
                                          match decode_uint 3 bytes with
                                          | None => None
                                          | Some (reserved_3_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; order_reference_number := order_reference_number_value; depth_side := depth_side_value; depth_order_capacity := depth_order_capacity_value; price_long := price_long_value; volume_long := volume_long_value; scope := scope_value; reserved_3 := reserved_3_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 36.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End AddOrderLongFormMessage.

  Module SingleSideExecutedMessage.

    (** This message is sent whenever a Side order is executed in whole or in part. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      order_reference_number : N;
      executed_volume : N;
      trade_condition : list byte;
      auction_id : N;
      cross_number : N;
      match_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (executed_volume record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (executed_volume record) ++
      encode_bytes 1 (trade_condition record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (executed_volume_value, bytes) =>
                          match decode_bytes 1 bytes with
                          | None => None
                          | Some (trade_condition_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (auction_id_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (cross_number_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (match_number_value, bytes) =>
                                          Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; order_reference_number := order_reference_number_value; executed_volume := executed_volume_value; trade_condition := trade_condition_value; auction_id := auction_id_value; cross_number := cross_number_value; match_number := match_number_value |}, bytes)
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 [bound_7 bound_8]]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_bytes by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideExecutedMessage.

  Module SingleSideExecutedWithPriceMessage.

    (** This message is sent whenever an incoming Side order is executed against the book in whole or in part at a price different from the initial display price. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      order_reference_number : N;
      cross_number : N;
      match_number : N;
      reserved_1 : N;
      price_long : N;
      volume_long : N;
      trade_condition : list byte;
      auction_id : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record) ++
      encode_bytes 1 (trade_condition record) ++
      encode_uint 4 (auction_id record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (cross_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (match_number_value, bytes) =>
                              match decode_uint 1 bytes with
                              | None => None
                              | Some (reserved_1_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_long_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (volume_long_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_condition_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (auction_id_value, bytes) =>
                                                  Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; order_reference_number := order_reference_number_value; cross_number := cross_number_value; match_number := match_number_value; reserved_1 := reserved_1_value; price_long := price_long_value; volume_long := volume_long_value; trade_condition := trade_condition_value; auction_id := auction_id_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 44.
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideExecutedWithPriceMessage.

  Module SingleSideReplaceShortFormMessage.

    (** This message is sent whenever an order on the book is replaced. The replacement has a new sequence number and replaces the prior sequence number. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      original_order_reference_number : N;
      new_order_reference_number : N;
      price_short : N;
      volume_short : N;
      order_type : list byte;
      scope : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (original_order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (new_order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (price_short record < 256 ^ N.of_nat 2)%N /\
      (volume_short record < 256 ^ N.of_nat 2)%N /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (scope record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (original_order_reference_number record) ++
      encode_uint 8 (new_order_reference_number record) ++
      encode_uint 2 (price_short record) ++
      encode_uint 2 (volume_short record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 1 (scope record) ++
      encode_uint 3 (reserved_3 record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (original_order_reference_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (new_order_reference_number_value, bytes) =>
                          match decode_uint 2 bytes with
                          | None => None
                          | Some (price_short_value, bytes) =>
                              match decode_uint 2 bytes with
                              | None => None
                              | Some (volume_short_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (order_type_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (scope_value, bytes) =>
                                          match decode_uint 3 bytes with
                                          | None => None
                                          | Some (reserved_3_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; original_order_reference_number := original_order_reference_number_value; new_order_reference_number := new_order_reference_number_value; price_short := price_short_value; volume_short := volume_short_value; order_type := order_type_value; scope := scope_value; reserved_3 := reserved_3_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideReplaceShortFormMessage.

  Module SingleSideReplaceLongFormMessage.

    (** This message is sent whenever an order on the book is replaced. The replacement has a new sequence number and replaces the prior sequence number. Long form. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      original_order_reference_number : N;
      new_order_reference_number : N;
      price_long : N;
      volume_long : N;
      order_type : list byte;
      scope : list byte;
      reserved_3 : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (original_order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (new_order_reference_number record < 256 ^ N.of_nat 8)%N /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_type record) = 1 /\
      Datatypes.length (scope record) = 1 /\
      (reserved_3 record < 256 ^ N.of_nat 3)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (original_order_reference_number record) ++
      encode_uint 8 (new_order_reference_number record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record) ++
      encode_bytes 1 (order_type record) ++
      encode_bytes 1 (scope record) ++
      encode_uint 3 (reserved_3 record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (original_order_reference_number_value, bytes) =>
                      match decode_uint 8 bytes with
                      | None => None
                      | Some (new_order_reference_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_long_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (order_type_value, bytes) =>
                                      match decode_bytes 1 bytes with
                                      | None => None
                                      | Some (scope_value, bytes) =>
                                          match decode_uint 3 bytes with
                                          | None => None
                                          | Some (reserved_3_value, bytes) =>
                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; original_order_reference_number := original_order_reference_number_value; new_order_reference_number := new_order_reference_number_value; price_long := price_long_value; volume_long := volume_long_value; order_type := order_type_value; scope := scope_value; reserved_3 := reserved_3_value |}, bytes)
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
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_uint by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      rewrite decode_encode_bytes by exact bound_8.
      rewrite decode_encode_uint by exact bound_9.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideReplaceLongFormMessage.

  Module SingleSideDeleteMessage.

    (** The message is sent when an order is being cancelled. All remaining contracts are no longer accessible so the side should be removed from the book. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id_order_reference : N;
      order_reference_number : N;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id_order_reference record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id_order_reference record) ++
      encode_uint 8 (order_reference_number record).

    Definition decode (bytes : list byte) : option (t * list byte) :=
      match decode_uint 2 bytes with
      | None => None
      | Some (tracking_number_value, bytes) =>
          match decode_uint 8 bytes with
          | None => None
          | Some (timestamp_value, bytes) =>
              match decode_uint 4 bytes with
              | None => None
              | Some (strategy_id_order_reference_value, bytes) =>
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id_order_reference := strategy_id_order_reference_value; order_reference_number := order_reference_number_value |}, bytes)
                  end
              end
          end
      end.

    Theorem encode_length : forall record, Datatypes.length (encode record) = 22.
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

  End SingleSideDeleteMessage.

  Module SingleSideUpdateMessage.

    (** This message is sent whenever an order is being updated for price and (or) contracts. The reference number associated with the order is unchanged. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      order_reference_number : N;
      change_reason : list byte;
      price_long : N;
      volume_long : N;
      order_type : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (order_reference_number record < 256 ^ N.of_nat 8)%N /\
      Datatypes.length (change_reason record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (order_type record) = 1.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 8 (order_reference_number record) ++
      encode_bytes 1 (change_reason record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record) ++
      encode_bytes 1 (order_type record).

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
                  match decode_uint 8 bytes with
                  | None => None
                  | Some (order_reference_number_value, bytes) =>
                      match decode_bytes 1 bytes with
                      | None => None
                      | Some (change_reason_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (price_long_value, bytes) =>
                              match decode_uint 4 bytes with
                              | None => None
                              | Some (volume_long_value, bytes) =>
                                  match decode_bytes 1 bytes with
                                  | None => None
                                  | Some (order_type_value, bytes) =>
                                      Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; order_reference_number := order_reference_number_value; change_reason := change_reason_value; price_long := price_long_value; volume_long := volume_long_value; order_type := order_type_value |}, bytes)
                                  end
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
      destruct bound as [bound_0 [bound_1 [bound_2 [bound_3 [bound_4 [bound_5 [bound_6 bound_7]]]]]]].
      unfold decode, encode.
      rewrite <- !app_assoc.
      rewrite decode_encode_uint by exact bound_0.
      rewrite decode_encode_uint by exact bound_1.
      rewrite decode_encode_uint by exact bound_2.
      rewrite decode_encode_uint by exact bound_3.
      rewrite decode_encode_bytes by exact bound_4.
      rewrite decode_encode_uint by exact bound_5.
      rewrite decode_encode_uint by exact bound_6.
      rewrite decode_encode_bytes by exact bound_7.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End SingleSideUpdateMessage.

  Module ComplexStrategyTradeMessage.

    (** This Options Trade Message is designed to provide execution details for normal match events involving non-display able order types. *)
    Record t := {
      tracking_number : N;
      timestamp : N;
      strategy_id : N;
      cross_number : N;
      match_number : N;
      reserved_4 : N;
      cross_type : list byte;
      price_long : N;
      volume_long : N;
      trade_condition : list byte;
      auction_id : N;
      reserved_1 : N;
      trade_type : list byte;
      reserved_16 : list byte;
    }.

    (** What its fields must hold for its bytes to read back as it *)
    Definition bounded (record : t) : Prop :=
      (tracking_number record < 256 ^ N.of_nat 2)%N /\
      (timestamp record < 256 ^ N.of_nat 8)%N /\
      (strategy_id record < 256 ^ N.of_nat 4)%N /\
      (cross_number record < 256 ^ N.of_nat 4)%N /\
      (match_number record < 256 ^ N.of_nat 4)%N /\
      (reserved_4 record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (cross_type record) = 1 /\
      (price_long record < 256 ^ N.of_nat 4)%N /\
      (volume_long record < 256 ^ N.of_nat 4)%N /\
      Datatypes.length (trade_condition record) = 1 /\
      (auction_id record < 256 ^ N.of_nat 4)%N /\
      (reserved_1 record < 256 ^ N.of_nat 1)%N /\
      Datatypes.length (trade_type record) = 1 /\
      Datatypes.length (reserved_16 record) = 16.

    Definition encode (record : t) : list byte :=
      encode_uint 2 (tracking_number record) ++
      encode_uint 8 (timestamp record) ++
      encode_uint 4 (strategy_id record) ++
      encode_uint 4 (cross_number record) ++
      encode_uint 4 (match_number record) ++
      encode_uint 4 (reserved_4 record) ++
      encode_bytes 1 (cross_type record) ++
      encode_uint 4 (price_long record) ++
      encode_uint 4 (volume_long record) ++
      encode_bytes 1 (trade_condition record) ++
      encode_uint 4 (auction_id record) ++
      encode_uint 1 (reserved_1 record) ++
      encode_bytes 1 (trade_type record) ++
      encode_bytes 16 (reserved_16 record).

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
                  match decode_uint 4 bytes with
                  | None => None
                  | Some (cross_number_value, bytes) =>
                      match decode_uint 4 bytes with
                      | None => None
                      | Some (match_number_value, bytes) =>
                          match decode_uint 4 bytes with
                          | None => None
                          | Some (reserved_4_value, bytes) =>
                              match decode_bytes 1 bytes with
                              | None => None
                              | Some (cross_type_value, bytes) =>
                                  match decode_uint 4 bytes with
                                  | None => None
                                  | Some (price_long_value, bytes) =>
                                      match decode_uint 4 bytes with
                                      | None => None
                                      | Some (volume_long_value, bytes) =>
                                          match decode_bytes 1 bytes with
                                          | None => None
                                          | Some (trade_condition_value, bytes) =>
                                              match decode_uint 4 bytes with
                                              | None => None
                                              | Some (auction_id_value, bytes) =>
                                                  match decode_uint 1 bytes with
                                                  | None => None
                                                  | Some (reserved_1_value, bytes) =>
                                                      match decode_bytes 1 bytes with
                                                      | None => None
                                                      | Some (trade_type_value, bytes) =>
                                                          match decode_bytes 16 bytes with
                                                          | None => None
                                                          | Some (reserved_16_value, bytes) =>
                                                              Some ({| tracking_number := tracking_number_value; timestamp := timestamp_value; strategy_id := strategy_id_value; cross_number := cross_number_value; match_number := match_number_value; reserved_4 := reserved_4_value; cross_type := cross_type_value; price_long := price_long_value; volume_long := volume_long_value; trade_condition := trade_condition_value; auction_id := auction_id_value; reserved_1 := reserved_1_value; trade_type := trade_type_value; reserved_16 := reserved_16_value |}, bytes)
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

    Theorem encode_length : forall record, Datatypes.length (encode record) = 58.
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
      rewrite decode_encode_uint by exact bound_7.
      rewrite decode_encode_uint by exact bound_8.
      rewrite decode_encode_bytes by exact bound_9.
      rewrite decode_encode_uint by exact bound_10.
      rewrite decode_encode_uint by exact bound_11.
      rewrite decode_encode_bytes by exact bound_12.
      rewrite decode_encode_bytes by exact bound_13.
      destruct record. reflexivity.
    Qed.

    Definition eq_dec : forall left right : t, {left = right} + {left <> right}.
    Proof. decide equality; solve [apply N.eq_dec | apply (list_eq_dec Byte.byte_eq_dec)]. Defined.

  End ComplexStrategyTradeMessage.

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

End IseOptionsSpreadDepthOfMarketV21Server.
